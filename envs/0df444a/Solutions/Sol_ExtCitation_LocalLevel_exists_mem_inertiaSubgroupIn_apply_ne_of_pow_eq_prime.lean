-- Prove2me | solution 1 for ExtCitation.LocalLevel.exists_mem_inertiaSubgroupIn_apply_ne_of_pow_eq_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/c4f00c09-7e1f-5602-8ad8-e82d493d473c

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_ExtCitation_InertiaKummerCharacter
import Theorems.Thm_ExtCitation_LocalLevel_norm_sum_smul_eq_of_linearIndependent_resw
import Theorems.Thm_ExtCitation_LocalLevel_finrank_le_of_forall_resw_pow_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_LocalLevel_exists_mem_inertiaSubgroupIn_apply_ne_of_pow_eq_prime

set_option autoImplicit false

open ExtCitation ExtCitation.LocalLevel
open scoped NNReal

namespace P2mS17R

variable (q : ℕ) [Fact q.Prime]

section ValueGroup

variable (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw]

noncomputable abbrev resHom : Rw q Kw →+* kbar q := (IsLocalRing.residue (OO q)).comp (algebraMap (Rw q Kw) (OO q))

theorem resHom_apply (x : Rw q Kw) : resHom q Kw x = resw q Kw x := rfl

theorem finite_range_resHom : (Set.range (resHom q Kw)).Finite := by
  haveI := finite_kM q (Module.finrank ℚ_[q] Kw).factorial (Nat.factorial_pos _)
  refine Set.Finite.subset (Set.toFinite ((kM q (Module.finrank ℚ_[q] Kw).factorial : Set (kbar q)))) ?_
  rintro _ ⟨x, rfl⟩
  exact residue_mem_kM q Kw x

noncomputable def kw : IntermediateField (ZMod q) (kbar q) where
  __ := (resHom q Kw).range
  algebraMap_mem' a := by
    refine ⟨(a.val : Rw q Kw), ?_⟩
    rw [map_natCast]
    change ((a.val : ℕ) : kbar q) = ZMod.cast a
    rw [ZMod.cast_eq_val]
  inv_mem' z hz := by
    rcases eq_or_ne z 0 with rfl | hz0
    · rw [inv_zero]; exact (resHom q Kw).range.zero_mem
    haveI : Finite ↥(resHom q Kw).range := (finite_range_resHom q Kw).to_subtype

    have hinj : Function.Injective (fun w : ↥(resHom q Kw).range => (⟨z * w, mul_mem hz w.2⟩ : ↥(resHom q Kw).range)) := by
      intro a b hab
      have := congrArg Subtype.val hab
      exact Subtype.ext (mul_left_cancel₀ hz0 this)
    obtain ⟨w, hw⟩ := Finite.surjective_of_injective hinj ⟨1, (resHom q Kw).range.one_mem⟩
    have hw' : z * w = 1 := congrArg Subtype.val hw
    rw [inv_eq_of_mul_eq_one_right hw']
    exact w.2

theorem mem_kw_iff {z : kbar q} : z ∈ kw q Kw ↔ z ∈ Set.range (resHom q Kw) := Iff.rfl

theorem resw_mem_kw (x : Rw q Kw) : resw q Kw x ∈ kw q Kw := ⟨x, rfl⟩

scoped instance finite_kw : Finite (kw q Kw) := (finite_range_resHom q Kw).to_subtype

theorem exists_norm_eq_zpow
    (hst : ∀ g : GG q, ∀ y : PadicAlgCl q, y ∈ Kw → g y ∈ Kw)
    (hI : ∀ w : GG q, (∀ x : OO q, ((w • x - x ^ 1 : OO q) : PadicAlgCl q) ∈ (padicIntegers q).nonunits) →
      ∀ y : PadicAlgCl q, y ∈ Kw → w y = y)
    (y : PadicAlgCl q) (hy : y ∈ Kw) (hy0 : y ≠ 0) : ∃ n : ℤ, ‖y‖ = (q : ℝ) ^ n := by
  classical

  set f : ℕ := Module.finrank (ZMod q) (kw q Kw) with hfdef
  have hf0 : 0 < f := Module.finrank_pos
  letI : Fintype (kw q Kw) := Fintype.ofFinite _
  have hcard : Fintype.card (kw q Kw) = q ^ f := by
    rw [Module.card_eq_pow_finrank (K := ZMod q) (V := kw q Kw), ZMod.card]
  have hfrob : ∀ x : Rw q Kw, resw q Kw x ^ (q ^ f) = resw q Kw x := by
    intro x
    have := FiniteField.pow_card (⟨resw q Kw x, resw_mem_kw q Kw x⟩ : kw q Kw)
    rw [hcard] at this
    exact congrArg Subtype.val this
  let bE := Module.finBasis (ZMod q) (kw q Kw)
  have hb : ∀ i : Fin f, ∃ x : Rw q Kw, resHom q Kw x = (bE i : kbar q) := fun i => (bE i).2
  choose yv hyv using hb
  have hli : LinearIndependent (ZMod q) (fun i => resw q Kw (yv i)) := by
    have : (fun i => resw q Kw (yv i)) = (kw q Kw).val.toLinearMap ∘ bE := by
      funext i; exact hyv i
    rw [this]
    exact bE.linearIndependent.map' _ (LinearMap.ker_eq_bot.mpr Subtype.val_injective)

  have hD1 : Module.finrank ℚ_[q] Kw ≤ f :=
    ExtCitation.LocalLevel.finrank_le_of_forall_resw_pow_eq q Kw hst hI f hf0 hfrob

  haveI : Nonempty (Fin f) := ⟨⟨0, hf0⟩⟩
  have hliK : LinearIndependent ℚ_[q] (fun i => (yv i : Kw)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    obtain ⟨j, hj⟩ := Finite.exists_max (fun i => ‖c i‖)
    have hE := ExtCitation.LocalLevel.norm_sum_smul_eq_of_linearIndependent_resw q Kw yv hli c j hj
    rw [hc, ZeroMemClass.coe_zero, norm_zero] at hE
    intro i
    exact norm_le_zero_iff.mp (hE ▸ hj i)
  have hcardf : Fintype.card (Fin f) = Module.finrank ℚ_[q] Kw :=
    le_antisymm (hliK.fintype_card_le_finrank) (by rw [Fintype.card_fin]; exact hD1)
  let B := basisOfLinearIndependentOfCardEqFinrank hliK hcardf

  set c : Fin f → ℚ_[q] := fun i => B.repr ⟨y, hy⟩ i with hcdef
  have hyexp : (⟨y, hy⟩ : Kw) = ∑ i, c i • (yv i : Kw) := by
    conv_lhs => rw [← B.sum_repr ⟨y, hy⟩]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  obtain ⟨j, hj⟩ := Finite.exists_max (fun i => ‖c i‖)
  have hE := ExtCitation.LocalLevel.norm_sum_smul_eq_of_linearIndependent_resw q Kw yv hli c j hj
  rw [← hyexp] at hE
  change ‖y‖ = ‖c j‖ at hE
  have hcj : c j ≠ 0 := by
    intro h0; rw [h0, norm_zero, norm_eq_zero] at hE; exact hy0 hE
  exact ⟨-(c j).valuation, by rw [hE, Padic.norm_eq_zpow_neg_valuation hcj]⟩

end ValueGroup

theorem zpow_pow_ne_inv {e : ℕ} (he : 2 ≤ e) (n : ℤ) : ((q : ℝ) ^ n) ^ e ≠ (q : ℝ)⁻¹ := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).one_lt
  intro h
  rw [← zpow_natCast, ← zpow_mul, ← zpow_neg_one] at h
  have hne : n * (e : ℤ) = -1 := zpow_right_injective₀ (zero_lt_one.trans hq1) hq1.ne' h
  by_cases hn : 0 ≤ n
  · have : 0 ≤ n * (e : ℤ) := mul_nonneg hn (by positivity)
    omega
  · have : n * (e : ℤ) ≤ -1 * (e : ℤ) := by
      apply mul_le_mul_of_nonneg_right (by omega) (by positivity)
    omega

theorem main {e : ℕ} (he : 2 ≤ e) (hqe : ¬ q ∣ e) {α : AlgebraicClosure ℚ}
    (hα : α ^ e = (q : AlgebraicClosure ℚ)) :
    ∃ t : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q,
      localGaloisToGlobal q t ∈ (padicPlace q).inertiaSubgroupIn ℚ ∧ localGaloisToGlobal q t α ≠ α := by
  classical
  by_contra hcon
  push Not at hcon
  have he0 : 0 < e := by omega
  have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  have hα0 : α ≠ 0 := by rintro rfl; rw [zero_pow he0.ne'] at hα; exact hq0 hα.symm

  let qq : Nat.Primes := ⟨q, Fact.out⟩
  have hroots : ∀ t : GG q, localGaloisToGlobal q t ∈ (padicPlace q).inertiaSubgroupIn ℚ →
      ∀ z : AlgebraicClosure ℚ, z ^ e = (q : AlgebraicClosure ℚ) → localGaloisToGlobal q t z = z := by
    intro t ht z hz
    have hζ : (z * α⁻¹) ^ e = 1 := by rw [mul_pow, inv_pow, hz, hα, mul_inv_cancel₀ hq0]
    have h1 : localGaloisToGlobal q t (z * α⁻¹) = z * α⁻¹ :=
      inertiaPullback_smul_eq_of_pow_eq_one qq (σ := t) ht hqe hζ
    calc localGaloisToGlobal q t z = localGaloisToGlobal q t (z * α⁻¹ * α) := by rw [inv_mul_cancel_right₀ hα0]
      _ = z := by rw [map_mul, h1, hcon t ht, inv_mul_cancel_right₀ hα0]

  let S₀ : Finset (AlgebraicClosure ℚ) := Polynomial.nthRootsFinset e ((q : ℕ) : AlgebraicClosure ℚ)
  have hS₀ : ∀ z, z ∈ S₀ ↔ z ^ e = (q : AlgebraicClosure ℚ) := fun z => Polynomial.mem_nthRootsFinset he0 _
  let S : Set (PadicAlgCl q) := padicEmbedding q '' (S₀ : Set (AlgebraicClosure ℚ))
  haveI : Finite S := ((S₀.finite_toSet).image _).to_subtype
  let Kw : IntermediateField ℚ_[q] (PadicAlgCl q) := IntermediateField.adjoin ℚ_[q] S
  haveI : FiniteDimensional ℚ_[q] Kw :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral

  have hSst : ∀ g : GG q, (g : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q) '' S ⊆ S := by
    rintro g _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨localGaloisToGlobal q g z, ?_, padicEmbedding_localGaloisToGlobal q g z⟩
    rw [Finset.mem_coe, hS₀] at hz ⊢
    rw [← map_pow, hz, map_natCast]
  have hst : ∀ g : GG q, ∀ y : PadicAlgCl q, y ∈ Kw → g y ∈ Kw := by
    intro g y hy
    have h1 : g y ∈ (Kw.map (g : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q) : Set (PadicAlgCl q)) := by
      rw [IntermediateField.coe_map]; exact ⟨y, hy, rfl⟩
    rw [IntermediateField.adjoin_map, SetLike.mem_coe] at h1
    exact IntermediateField.adjoin.mono _ _ _ (hSst g) h1

  have hI : ∀ w : GG q, (∀ x : OO q, ((w • x - x ^ 1 : OO q) : PadicAlgCl q) ∈ (padicIntegers q).nonunits) →
      ∀ y : PadicAlgCl q, y ∈ Kw → w y = y := by
    intro w hw y hy
    have hwI : localGaloisToGlobal q w ∈ (padicPlace q).inertiaSubgroupIn ℚ :=
      mem_inertiaPullback_of_smul_sub_mem q w hw
    let Fw : IntermediateField ℚ_[q] (PadicAlgCl q) :=
      (FixedBy.subfield (PadicAlgCl q) w).toIntermediateField fun r => by
        rw [FixedBy.subfield_mem_iff, AlgEquiv.smul_def]; exact w.commutes r
    have hSF : S ⊆ Fw := by
      rintro _ ⟨z, hz, rfl⟩
      rw [Finset.mem_coe, hS₀] at hz
      show padicEmbedding q z ∈ FixedBy.subfield (PadicAlgCl q) w
      rw [FixedBy.subfield_mem_iff, AlgEquiv.smul_def, ← padicEmbedding_localGaloisToGlobal, hroots w hwI z hz]
    have hy' : y ∈ Fw := IntermediateField.adjoin_le_iff.mpr hSF hy
    have : w • y = y := (FixedBy.subfield_mem_iff (PadicAlgCl q) w y).mp hy'
    rwa [AlgEquiv.smul_def] at this

  set β : PadicAlgCl q := padicEmbedding q α with hβdef
  have hαS : α ∈ S₀ := (hS₀ α).mpr hα
  have hβK : β ∈ Kw := IntermediateField.subset_adjoin ℚ_[q] S ⟨α, Finset.mem_coe.mpr hαS, rfl⟩
  have hβ0 : β ≠ 0 := (map_ne_zero (padicEmbedding q)).mpr hα0
  obtain ⟨n, hn⟩ := exists_norm_eq_zpow q Kw hst hI β hβK hβ0

  have hβe : ‖β‖ ^ e = (q : ℝ)⁻¹ := by
    rw [← norm_pow, hβdef, ← map_pow, hα, map_natCast, ← map_natCast (algebraMap ℚ_[q] (PadicAlgCl q)) q]
    change ‖((q : ℚ_[q]) : PadicAlgCl q)‖ = _
    rw [PadicAlgCl.norm_extends, Padic.norm_p]
  rw [hn] at hβe
  exact zpow_pow_ne_inv q he n hβe

end P2mS17R
p2m_reactivate "P2MW.S_ExtCitation_LocalLevel_exists_mem_inertiaSubgroupIn_apply_ne_of_pow_eq_prime.P2mS17R"

open ExtCitation ExtCitation.LocalLevel in
theorem solution (q : ℕ) [Fact q.Prime] {e : ℕ} (he : 2 ≤ e) (hqe : ¬ q ∣ e)
    {α : AlgebraicClosure ℚ} (hα : α ^ e = (q : AlgebraicClosure ℚ)) :
    ∃ t : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q,
      localGaloisToGlobal q t ∈ (padicPlace q).inertiaSubgroupIn ℚ ∧ localGaloisToGlobal q t α ≠ α :=
  P2mS17R.main q he hqe hα

end S_ExtCitation_LocalLevel_exists_mem_inertiaSubgroupIn_apply_ne_of_pow_eq_prime
end P2MW
export P2MW.S_ExtCitation_LocalLevel_exists_mem_inertiaSubgroupIn_apply_ne_of_pow_eq_prime (solution)
