-- Prove2me | solution 1 for ExtCitation.LocalLevel.exists_frobenius_uniformiser_inf_level
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/3915f36b-0eb5-5640-ae7a-e7cd6c556d36

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_GroupCohomology_CyclicCarry
import Theorems.Thm_ExtCitation_LocalLevel_mem_adjoin_rootsOfUnity_of_forall_inf_smul_eq
import Theorems.Thm_ExtCitation_LocalLevel_mem_of_unramified_level_of_forall_norm_smul_sub_lt_one
import Theorems.Thm_IntermediateField_exists_uniformiser_padic
import Theorems.Thm_IntermediateField_exists_norm_eq_adjoin_rootsOfUnity_padic
import Theorems.Thm_IntermediateField_finrank_adjoin_rootsOfUnity_padic_eq_orderOf
import Theorems.Thm_IntermediateField_finiteDimensional_normal_adjoin_rootsOfUnity_padic
import Theorems.Thm_ExtCitation_LocalLevel_finite_residueField_Rw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_LocalLevel_exists_frobenius_uniformiser_inf_level

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory groupCohomology ExtCitation.LocalLevel

set_option maxHeartbeats 800000

namespace AUXProof

variable (q : ℕ) [Fact q.Prime]

lemma norm_lt_one_of_mem_nonunits {y : PadicAlgCl q} (hy : y ∈ (padicIntegers q).nonunits) : ‖y‖ < 1 := by
  rw [ValuationSubring.mem_nonunits_iff, ← (Valuation.isEquiv_valuation_valuationSubring _).lt_one_iff_lt_one] at hy
  change Valued.v y < 1 at hy
  have : (‖y‖₊ : ℝ) < 1 := by exact_mod_cast hy
  simpa using this

lemma norm_natCast_eq_one {m : ℕ} (hm : ¬ q ∣ m) : ‖(m : PadicAlgCl q)‖ = 1 := by
  rw [← map_natCast (algebraMap ℚ_[q] (PadicAlgCl q)) m]
  change ‖((m : ℚ_[q]) : PadicAlgCl q)‖ = 1
  rw [PadicAlgCl.norm_extends, Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hm

lemma not_dvd_pow_sub_one {N : ℕ} (hN : 0 < N) : ¬ q ∣ q ^ N - 1 := by
  intro h
  have hq : q ∣ q ^ N := dvd_pow_self q hN.ne'
  have h1 : 1 ≤ q ^ N := Nat.one_le_pow _ _ (Fact.out : q.Prime).pos
  have : q ∣ q ^ N - (q ^ N - 1) := Nat.dvd_sub hq h
  rw [Nat.sub_sub_self h1] at this
  exact (Fact.out : q.Prime).one_lt.ne' (Nat.dvd_one.1 this)

variable (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]

lemma under_maximalIdeal_Rw :
    (IsLocalRing.maximalIdeal (OO q)).under (Rw q K) = IsLocalRing.maximalIdeal (Rw q K) := by
  ext x
  show x ∈ Ideal.comap (algebraMap (Rw q K) (OO q)) (IsLocalRing.maximalIdeal (OO q)) ↔ _
  rw [Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff (A := padicIntegers q),
    ← ValuationSubring.coe_mem_nonunits_iff (A := Rw q K), algebraMap_Rw_coe]
  exact (mem_nonunits_comap (B := padicIntegers q) (f := algebraMap K (PadicAlgCl q)) (x := (x : K))).symm

lemma exists_frob_over (hfin : Finite (IsLocalRing.ResidueField (Rw q K))) :
    ∃ σ : Gw q K,
      (∀ x : OO q, ‖((σ : GG q) (x : PadicAlgCl q)) -
        (x : PadicAlgCl q) ^ Nat.card (IsLocalRing.ResidueField (Rw q K))‖ < 1) ∧
      (∀ (ζ : OO q) (m : ℕ), ¬ q ∣ m → ζ ^ m = 1 →
        (σ : GG q) (ζ : PadicAlgCl q) = (ζ : PadicAlgCl q) ^ Nat.card (IsLocalRing.ResidueField (Rw q K))) := by
  haveI : Algebra.IsIntegral ℚ_[q] (PadicAlgCl q) := ⟨fun x => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral⟩
  let Q := IsLocalRing.maximalIdeal (OO q)
  have hP : Q.under (Rw q K) = IsLocalRing.maximalIdeal (Rw q K) := under_maximalIdeal_Rw q K
  haveI : Finite (Rw q K ⧸ Q.under (Rw q K)) := by rw [hP]; exact hfin
  have hcard : Nat.card (Rw q K ⧸ Q.under (Rw q K)) = Nat.card (IsLocalRing.ResidueField (Rw q K)) := by
    rw [hP]; rfl
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant_of_profinite (Rw q K) (Gw q K) Q
  refine ⟨σ, fun x => ?_, fun ζ m hm hζ => ?_⟩
  · have hx := hσ x
    rw [hcard] at hx
    have := norm_lt_one_of_mem_nonunits q (ValuationSubring.coe_mem_nonunits_iff.mpr hx)
    simp at this
    exact this
  · have hmQ : ((m : ℕ) : OO q) ∉ Q := by
      intro hmem
      have h := norm_lt_one_of_mem_nonunits q (ValuationSubring.coe_mem_nonunits_iff.mpr hmem)
      have e : (((m : ℕ) : OO q) : PadicAlgCl q) = (m : PadicAlgCl q) := by simp
      rw [e, norm_natCast_eq_one q hm] at h
      exact lt_irrefl _ h
    have h := AlgHom.IsArithFrobAt.apply_of_pow_eq_one hσ hζ hmQ
    rw [hcard] at h
    have h' := congrArg (fun y : OO q => (y : PadicAlgCl q)) h
    simp at h'
    exact h'

noncomputable section
open Polynomial

section Layer

variable (K : IntermediateField ℚ_[q] (PadicAlgCl q))
  (L : IntermediateField ℚ_[q] (PadicAlgCl q))
  (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
  (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
  (hKL : K ≤ L) (hK : ∀ x : L, (x : PadicAlgCl q) ∈ K ↔ ∀ g : G, g • x = x)

omit [FaithfulSMul G L] in
include hK in

theorem stable (σ : GG q) (hσ : ∀ k ∈ K, σ k = k) (x : L) : σ (x : PadicAlgCl q) ∈ L := by
  classical
  letI := Fintype.ofFinite G
  let p : L[X] := prodXSubSMul G L x
  have hpcoeff : ∀ i, ((p.coeff i : L) : PadicAlgCl q) ∈ K := fun i =>
    (hK _).2 (fun g => prodXSubSMul.coeff G L x g i)
  let P : (PadicAlgCl q)[X] := p.map (algebraMap L (PadicAlgCl q))
  have hPσ : P.map (σ : PadicAlgCl q →+* PadicAlgCl q) = P := by
    ext i
    simp only [P, Polynomial.coeff_map]
    exact hσ _ (hpcoeff i)
  have hroot : P.eval (x : PadicAlgCl q) = 0 := by
    show (p.map (algebraMap L (PadicAlgCl q))).eval (algebraMap L (PadicAlgCl q) x) = 0
    rw [Polynomial.eval_map, Polynomial.eval₂_hom, prodXSubSMul.eval, map_zero]
  have hroot' : P.eval (σ (x : PadicAlgCl q)) = 0 := by
    rw [← hPσ, Polynomial.eval_map, show σ (x : PadicAlgCl q) = (σ : PadicAlgCl q →+* PadicAlgCl q) x from rfl,
      Polynomial.eval₂_hom, hroot, map_zero]
  simp only [P, p, prodXSubSMul, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    Finset.prod_eq_zero_iff] at hroot'
  obtain ⟨g, -, hg⟩ := hroot'
  rw [sub_eq_zero] at hg
  rw [hg]
  exact Subtype.mem _

include hK in

theorem exists_restrict (σ : GG q) (hσ : ∀ k ∈ K, σ k = k) :
    ∃ g : G, ∀ x : L, ((g • x : L) : PadicAlgCl q) = σ (x : PadicAlgCl q) := by
  have hst := stable q K L G hK σ hσ
  let ψ₀ : L →+* L :=
    { toFun := fun x => ⟨σ (x : PadicAlgCl q), hst x⟩
      map_one' := Subtype.ext (map_one σ)
      map_mul' := fun x y => Subtype.ext (map_mul σ _ _)
      map_zero' := Subtype.ext (map_zero σ)
      map_add' := fun x y => Subtype.ext (map_add σ _ _) }
  let ψ : L →ₐ[FixedPoints.subfield G L] L :=
    { toRingHom := ψ₀
      commutes' := fun c => by
        apply Subtype.ext
        show σ ((c : L) : PadicAlgCl q) = ((c : L) : PadicAlgCl q)
        exact hσ _ ((hK (c : L)).2 (fun g => c.2 g)) }
  obtain ⟨g, hg⟩ := (FixedPoints.toAlgHom_bijective G L).2 ψ
  refine ⟨g, fun x => ?_⟩
  exact congrArg Subtype.val (show g • x = ψ x from congrArg (fun f : L →ₐ[FixedPoints.subfield G L] L => f x) hg)

omit [Finite G] [FaithfulSMul G L] in
include hG hKL hK in

theorem exists_extend (g : G) :
    ∃ σ : GG q, (∀ k ∈ K, σ k = k) ∧ ∀ x : L, σ (x : PadicAlgCl q) = ((g • x : L) : PadicAlgCl q) := by
  haveI : IsGalois ℚ_[q] (PadicAlgCl q) := IsAlgClosure.isGalois ℚ_[q] (PadicAlgCl q)
  let gA : L ≃ₐ[ℚ_[q]] L :=
    { MulSemiringAction.toRingEquiv G L g with commutes' := hG g }
  refine ⟨gA.liftNormal (PadicAlgCl q), fun k hk => ?_, fun x => ?_⟩
  · have h := AlgEquiv.liftNormal_commutes gA (PadicAlgCl q) ⟨k, hKL hk⟩
    have hfix : g • (⟨k, hKL hk⟩ : L) = ⟨k, hKL hk⟩ := (hK ⟨k, hKL hk⟩).1 hk g
    have h' : (gA ⟨k, hKL hk⟩ : L) = ⟨k, hKL hk⟩ := hfix
    rw [h'] at h
    exact h
  · exact AlgEquiv.liftNormal_commutes gA (PadicAlgCl q) x

theorem normal_of_stable (hst : ∀ σ : GG q, (∀ k ∈ K, σ k = k) → ∀ y ∈ L, σ y ∈ L) :
    ((Gw q L).subgroupOf (Gw q K)).Normal := by
  refine ⟨fun a ha σ => ?_⟩
  rw [Subgroup.mem_subgroupOf] at ha ⊢
  rw [IntermediateField.mem_fixingSubgroup_iff] at ha ⊢
  intro y hy
  have hσ' : ∀ k ∈ K, ((σ⁻¹ : Gw q K) : GG q) k = k := (IntermediateField.mem_fixingSubgroup_iff K _).1 (σ⁻¹).2
  have hy' : ((σ⁻¹ : Gw q K) : GG q) y ∈ L := hst _ hσ' y hy
  show (σ : GG q) ((a : GG q) (((σ⁻¹ : Gw q K) : GG q) y)) = y
  rw [ha _ hy']
  show ((σ * σ⁻¹ : Gw q K) : GG q) y = y
  rw [mul_inv_cancel]
  rfl

omit [FaithfulSMul G L] in
include hK in
theorem normal_subgroupOf :
    ((Gw q L).subgroupOf (Gw q K)).Normal :=
  normal_of_stable q K L (fun σ hσ y hy => stable q K L G hK σ hσ ⟨y, hy⟩)

noncomputable def rHom : Gw q K →* G where
  toFun σ := Classical.choose (exists_restrict q K L G hK σ ((IntermediateField.mem_fixingSubgroup_iff K _).1 σ.2))
  map_one' := by
    apply FaithfulSMul.eq_of_smul_eq_smul (α := L)
    intro x
    apply Subtype.ext
    rw [Classical.choose_spec (exists_restrict q K L G hK (1 : Gw q K) ((IntermediateField.mem_fixingSubgroup_iff K _).1 (1 : Gw q K).2)) x, one_smul]
    rfl
  map_mul' σ τ := by
    apply FaithfulSMul.eq_of_smul_eq_smul (α := L)
    intro x
    apply Subtype.ext
    rw [Classical.choose_spec (exists_restrict q K L G hK (σ * τ) ((IntermediateField.mem_fixingSubgroup_iff K _).1 (σ * τ).2)) x, mul_smul,
      Classical.choose_spec (exists_restrict q K L G hK σ ((IntermediateField.mem_fixingSubgroup_iff K _).1 σ.2)),
      Classical.choose_spec (exists_restrict q K L G hK τ ((IntermediateField.mem_fixingSubgroup_iff K _).1 τ.2))]
    rfl

theorem rHom_spec (σ : Gw q K) (x : L) :
    ((rHom q K L G hK σ • x : L) : PadicAlgCl q) = (σ : GG q) (x : PadicAlgCl q) :=
  Classical.choose_spec (exists_restrict q K L G hK σ ((IntermediateField.mem_fixingSubgroup_iff K _).1 σ.2)) x

theorem rHom_eq_one_iff (σ : Gw q K) : rHom q K L G hK σ = 1 ↔ (σ : GG q) ∈ Gw q L := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h y hy
    have := rHom_spec q K L G hK σ ⟨y, hy⟩
    rw [h, one_smul] at this
    exact this.symm
  · intro h
    apply FaithfulSMul.eq_of_smul_eq_smul (α := L)
    intro x
    apply Subtype.ext
    rw [rHom_spec, one_smul]
    exact h _ x.2

include hG hKL in
theorem rHom_surjective : Function.Surjective (rHom q K L G hK) := by
  intro g
  obtain ⟨σ, hσK, hσ⟩ := exists_extend q K L G hG hKL hK g
  refine ⟨⟨σ, (IntermediateField.mem_fixingSubgroup_iff K σ).2 hσK⟩, ?_⟩
  apply FaithfulSMul.eq_of_smul_eq_smul (α := L)
  intro x
  apply Subtype.ext
  rw [rHom_spec]
  exact hσ x

end Layer

theorem cyclotomic_frobenius (K' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K']
    (N₀ : ℕ) (hN₀ : 0 < N₀) :
    ∃ σ : Gw q K',
      (∀ x : OO q, ‖((σ : GG q) (x : PadicAlgCl q)) -
        (x : PadicAlgCl q) ^ Nat.card (IsLocalRing.ResidueField (Rw q K'))‖ < 1) ∧
      (∀ γ : Gw q K', ∃ j : ℕ, ∀ y : PadicAlgCl q,
        y ∈ IntermediateField.adjoin K' {ζ : PadicAlgCl q | ζ ^ (q ^ N₀ - 1) = 1} →
          (γ : GG q) y = ((σ : GG q) ^ j) y) := by
  classical
  obtain ⟨hfdE, hnormE⟩ := IntermediateField.finiteDimensional_normal_adjoin_rootsOfUnity_padic q K' N₀ hN₀
  have hdeg' := IntermediateField.finrank_adjoin_rootsOfUnity_padic_eq_orderOf q K' N₀ hN₀
  set E : IntermediateField K' (PadicAlgCl q) :=
    IntermediateField.adjoin K' {ζ : PadicAlgCl q | ζ ^ (q ^ N₀ - 1) = 1} with hE
  haveI := hfdE
  haveI := hnormE
  haveI : IsGalois K' E := isGalois_iff.2 ⟨inferInstance, hnormE⟩
  haveI hfin : Finite (IsLocalRing.ResidueField (Rw q K')) := ExtCitation.LocalLevel.finite_residueField_Rw q K'
  set Q : ℕ := Nat.card (IsLocalRing.ResidueField (Rw q K')) with hQ
  have hQpos : 0 < Q := Nat.card_pos
  have hΓcard : Nat.card (E ≃ₐ[K'] E) = orderOf ((Q : ZMod (q ^ N₀ - 1))) := by
    rw [IsGalois.card_aut_eq_finrank, hdeg']

  obtain ⟨σ, hσ, hσroot⟩ := exists_frob_over q K' hfin
  have toK : ∀ γ : Gw q K', ∃ γK : PadicAlgCl q ≃ₐ[K'] PadicAlgCl q, ∀ y, γK y = (γ : GG q) y := fun γ =>
    ⟨AlgEquiv.ofRingEquiv (f := ((γ : GG q) : PadicAlgCl q ≃+* PadicAlgCl q))
      (fun k => (IntermediateField.mem_fixingSubgroup_iff K' (γ : GG q)).1 γ.2 k k.2), fun _ => rfl⟩
  obtain ⟨σK, hσK'⟩ := toK σ
  let φ : E ≃ₐ[K'] E := AlgEquiv.restrictNormalHom E σK
  have hφ : ∀ x : E, ((φ x : E) : PadicAlgCl q) = (σ : GG q) (x : PadicAlgCl q) := fun x => by
    rw [← hσK']; exact AlgEquiv.restrictNormalHom_apply E σK x

  have hM : ¬ q ∣ q ^ N₀ - 1 := not_dvd_pow_sub_one q hN₀
  have hMpos : 0 < q ^ N₀ - 1 := by
    have : 2 ≤ q ^ N₀ := le_trans (Fact.out : q.Prime).two_le (Nat.le_self_pow hN₀.ne' q)
    omega
  haveI : NeZero ((q ^ N₀ - 1 : ℕ) : ℚ_[q]) := ⟨by exact_mod_cast hMpos.ne'⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl q) (q ^ N₀ - 1)
  have hζ₀E : ζ₀ ∈ E := IntermediateField.subset_adjoin K' _ (show ζ₀ ^ (q ^ N₀ - 1) = 1 from hζ₀.pow_eq_one)
  have hζ₀norm : ‖ζ₀‖ = 1 := by
    have h := congrArg norm hζ₀.pow_eq_one
    rw [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hMpos.ne').1 h
  have hζ₀int : ζ₀ ∈ padicIntegers q := by
    rw [mem_padicIntegers_iff, ← NNReal.coe_le_coe, coe_nnnorm, hζ₀norm]; rfl
  have hζ₀ne : ζ₀ ≠ 0 := hζ₀.ne_zero hMpos.ne'
  set z : E := ⟨ζ₀, hζ₀E⟩ with hz
  have hσζ : (σ : GG q) ζ₀ = ζ₀ ^ Q := by
    have := hσroot ⟨ζ₀, hζ₀int⟩ (q ^ N₀ - 1) hM (Subtype.ext (by simpa using hζ₀.pow_eq_one))
    simpa using this
  have hφz : φ z = z ^ Q := by
    apply Subtype.ext
    rw [hφ]
    simpa [hz] using hσζ
  have hφjz : ∀ j : ℕ, (((φ ^ j) z : E) : PadicAlgCl q) = ζ₀ ^ (Q ^ j) := by
    intro j
    induction j with
    | zero => simp [hz]
    | succ j ih =>
      rw [pow_succ, AlgEquiv.mul_apply, hφz, map_pow]
      push_cast
      rw [ih, ← pow_mul, ← pow_succ]

  have hord : orderOf φ = Nat.card (E ≃ₐ[K'] E) := by
    apply Nat.dvd_antisymm (orderOf_dvd_natCard φ)
    rw [hΓcard]
    apply orderOf_dvd_of_pow_eq_one
    have h1 : ((φ ^ orderOf φ) z : E) = z := by rw [pow_orderOf_eq_one]; rfl
    have h2 : ζ₀ ^ (Q ^ orderOf φ) = ζ₀ := by rw [← hφjz, h1]
    have h1Q : 1 ≤ Q ^ orderOf φ := Nat.one_le_pow _ _ hQpos
    have h3 : ζ₀ ^ (Q ^ orderOf φ - 1) = 1 := by
      have e : ζ₀ ^ (Q ^ orderOf φ - 1) * ζ₀ = 1 * ζ₀ := by
        rw [← pow_succ, Nat.sub_add_cancel h1Q, h2, one_mul]
      exact mul_right_cancel₀ hζ₀ne e
    have h4 : (q ^ N₀ - 1) ∣ Q ^ orderOf φ - 1 := (hζ₀.pow_eq_one_iff_dvd _).1 h3
    have h5 : ((Q ^ orderOf φ - 1 : ℕ) : ZMod (q ^ N₀ - 1)) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h4
    rw [Nat.cast_sub h1Q, Nat.cast_pow, Nat.cast_one, sub_eq_zero] at h5
    exact h5
  have htop : Subgroup.zpowers φ = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hord])

  have hφpow : ∀ (j : ℕ) (x : E), (((φ ^ j) x : E) : PadicAlgCl q) = ((σ : GG q) ^ j) (x : PadicAlgCl q) := by
    intro j
    induction j with
    | zero => intro x; rfl
    | succ j ih =>
      intro x
      rw [pow_succ', pow_succ', AlgEquiv.mul_apply, AlgEquiv.mul_apply, hφ, ih]
  refine ⟨σ, hσ, fun γ => ?_⟩
  obtain ⟨γK, hγK⟩ := toK γ
  have hmem : AlgEquiv.restrictNormalHom E γK ∈ Subgroup.zpowers φ := by
    rw [htop]; exact Subgroup.mem_top _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hopos : (0 : ℤ) < (orderOf φ : ℤ) := by exact_mod_cast orderOf_pos φ
  refine ⟨(k % (orderOf φ : ℤ)).toNat, fun y hy => ?_⟩
  have hj : φ ^ (k % (orderOf φ : ℤ)).toNat = AlgEquiv.restrictNormalHom E γK := by
    rw [← hk, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ hopos.ne'), zpow_mod_orderOf]
  have h1 : (((AlgEquiv.restrictNormalHom E γK) ⟨y, hy⟩ : E) : PadicAlgCl q) = γK y :=
    AlgEquiv.restrictNormalHom_apply E γK ⟨y, hy⟩
  rw [hγK] at h1
  rw [← h1, ← hj, hφpow]

section Gen

variable (L : IntermediateField ℚ_[q] (PadicAlgCl q))
  (G : Type) [Group G] [Finite G] [MulSemiringAction G L]
  (S : Subgroup G) [FaithfulSMul S L]
  (K' : IntermediateField ℚ_[q] (PadicAlgCl q))
  (hGS : ∀ (s : S) (x : ℚ_[q]), s • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
  (hK'L : K' ≤ L) (hKS : ∀ x : L, (x : PadicAlgCl q) ∈ K' ↔ ∀ s : S, s • x = x)
  (N : Subgroup G) [N.Normal] (N₀ : ℕ)
  (σ : Gw q K')
  (hσgen : ∀ γ : Gw q K', ∃ j : ℕ, ∀ y : PadicAlgCl q,
    y ∈ IntermediateField.adjoin K' {ζ : PadicAlgCl q | ζ ^ (q ^ N₀ - 1) = 1} → (γ : GG q) y = ((σ : GG q) ^ j) y)
  (hstar : ∀ x : L, (∀ n ∈ N ⊓ S, n • x = x) →
    (x : PadicAlgCl q) ∈ IntermediateField.adjoin K' {ζ : PadicAlgCl q | ζ ^ (q ^ N₀ - 1) = 1})
  (hIT : ∀ g : G, (∀ x : L, (∀ n ∈ N, n • x = x) → g • x = x) → g ∈ N)

include hGS hK'L hσgen hstar hIT in

theorem generator_of_level :
    ∀ g : S ⧸ N.subgroupOf S, g ∈ Subgroup.zpowers (QuotientGroup.mk' (N.subgroupOf S) (rHom q K' L S hKS σ)) := by
  intro g
  induction g using QuotientGroup.induction_on with | H s =>
  obtain ⟨γ, hγ⟩ := rHom_surjective q K' L S hGS hK'L hKS s
  obtain ⟨j, hagree⟩ := hσgen γ

  have hsx : ∀ x : L, (∀ n ∈ N ⊓ S, n • x = x) → (s : G) • x = ((rHom q K' L S hKS σ : G) ^ j) • x := by
    intro x hx
    apply Subtype.ext
    have e1 : (((s : G) • x : L) : PadicAlgCl q) = (γ : GG q) (x : PadicAlgCl q) := by
      rw [← hγ]; exact rHom_spec q K' L S hKS γ x
    have e2 : ((((rHom q K' L S hKS σ : G) ^ j) • x : L) : PadicAlgCl q) = ((σ : GG q) ^ j) (x : PadicAlgCl q) := by
      have := rHom_spec q K' L S hKS (σ ^ j) x
      rw [map_pow, Subgroup.coe_pow] at this
      rw [← this, ← Subgroup.coe_pow]
      rfl
    rw [e1, e2]
    exact hagree _ (hstar x hx)

  have ht : ((((rHom q K' L S hKS σ) ^ j)⁻¹ * s : S) : G) ∈ N := by
    apply hIT
    intro x hxN
    have hx' : ∀ n ∈ N ⊓ S, n • x = x := fun n hn => hxN n hn.1
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, mul_smul, hsx x hx', ← mul_smul,
      inv_mul_cancel, one_smul]
  have hcls : (QuotientGroup.mk s : S ⧸ N.subgroupOf S) =
      (QuotientGroup.mk' (N.subgroupOf S) (rHom q K' L S hKS σ)) ^ j := by
    rw [← map_pow, QuotientGroup.mk'_apply, eq_comm, QuotientGroup.eq]
    exact Subgroup.mem_subgroupOf.2 ht
  rw [hcls]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) j

end Gen

end

end AUXProof

open AUXProof in
theorem solution (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    [MulDistribMulAction G (↥L)ˣ]
    (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L))
    (S : Subgroup G)
    (K' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K'] (hK'L : K' ≤ L)
    (hK' : ∀ x : L, (x : PadicAlgCl q) ∈ K' ↔ ∀ s ∈ S, s • x = x)
    (N : Subgroup G) [N.Normal]
    (π : (↥L)ˣ) (hπG : ∀ g : G, g • π = π) (hπ1 : ‖((π : L) : PadicAlgCl q)‖ < 1)
    (hπmax : ∀ y : L, (∀ n ∈ N, n • y = y) → ‖(y : PadicAlgCl q)‖ < 1 → ‖(y : PadicAlgCl q)‖ ≤ ‖((π : L) : PadicAlgCl q)‖) :
    ∃ (ψ : S) (π' : (↥L)ˣ),
      (∀ g : S ⧸ N.subgroupOf S, g ∈ Subgroup.zpowers (QuotientGroup.mk' (N.subgroupOf S) ψ)) ∧
      (∀ x : L, (∀ n ∈ N ⊓ S, n • x = x) → ‖(x : PadicAlgCl q)‖ ≤ 1 →
        ‖(((ψ : G) • x : L) : PadicAlgCl q) - (x : PadicAlgCl q) ^ Nat.card (IsLocalRing.ResidueField (Rw q K'))‖ < 1) ∧
      (∀ s ∈ S, s • π' = π') ∧ ‖((π' : L) : PadicAlgCl q)‖ < 1 ∧
      (∀ y : L, (∀ n ∈ N ⊓ S, n • y = y) → ‖(y : PadicAlgCl q)‖ < 1 → ‖(y : PadicAlgCl q)‖ ≤ ‖((π' : L) : PadicAlgCl q)‖) := by
  classical
  haveI : IsGalois ℚ_[q] (PadicAlgCl q) := IsAlgClosure.isGalois ℚ_[q] (PadicAlgCl q)

  haveI : FaithfulSMul S L := ⟨fun {s t} h => Subtype.ext (FaithfulSMul.eq_of_smul_eq_smul (M := G) (α := L) h)⟩
  have hKS : ∀ x : L, (x : PadicAlgCl q) ∈ K' ↔ ∀ s : S, s • x = x :=
    fun x => (hK' x).trans ⟨fun h s => h s s.2, fun h s hs => h ⟨s, hs⟩⟩
  have hGS : ∀ (s : S) (x : ℚ_[q]), s • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x := fun s x => hG s x

  have hπG' : ∀ g : G, g • (π : L) = (π : L) := fun g => by rw [← hcompat, hπG]
  obtain ⟨N₀, hN₀, hstar⟩ := ExtCitation.LocalLevel.mem_adjoin_rootsOfUnity_of_forall_inf_smul_eq q L G hG S K' hK'L hK' N
    (π : L) hπG' hπ1 hπmax
  have hIT : ∀ g : G, (∀ x : L, (∀ n ∈ N, n • x = x) → g • x = x) → g ∈ N := by
    intro g hg
    apply ExtCitation.LocalLevel.mem_of_unramified_level_of_forall_norm_smul_sub_lt_one q L G hG N (π : L)
      hπG' hπ1 hπmax
    intro x hxN _
    rw [hg x hxN, sub_self, norm_zero]
    exact zero_lt_one

  obtain ⟨σ, hσ, hσgen⟩ := cyclotomic_frobenius q K' N₀ hN₀
  have hψ : ∀ x : L, ((((rHom q K' L S hKS σ : G)) • x : L) : PadicAlgCl q) = (σ : GG q) (x : PadicAlgCl q) :=
    fun x => rHom_spec q K' L S hKS σ x

  obtain ⟨π₀, hπ₀pos, hπ₀lt, hπ₀val⟩ := IntermediateField.exists_uniformiser_padic q K'
  have hπ₀L : ((π₀ : K') : PadicAlgCl q) ∈ L := hK'L π₀.2
  have hπ₀ne : (⟨(π₀ : PadicAlgCl q), hπ₀L⟩ : L) ≠ 0 := by
    intro h
    have : (π₀ : PadicAlgCl q) = 0 := congrArg Subtype.val h
    rw [this, norm_zero] at hπ₀pos
    exact lt_irrefl _ hπ₀pos
  refine ⟨rHom q K' L S hKS σ, Units.mk0 ⟨(π₀ : PadicAlgCl q), hπ₀L⟩ hπ₀ne,
    generator_of_level q L G S K' hGS hK'L hKS N N₀ σ hσgen hstar hIT, ?_, ?_, ?_, ?_⟩
  ·
    intro x _ hx
    have hxint : (x : PadicAlgCl q) ∈ padicIntegers q := by
      rw [mem_padicIntegers_iff, ← NNReal.coe_le_coe, coe_nnnorm]; exact hx
    have h := hσ ⟨(x : PadicAlgCl q), hxint⟩
    rw [hψ]
    exact h
  ·
    intro s hs
    apply Units.ext
    rw [hcompat]
    show s • (⟨(π₀ : PadicAlgCl q), hπ₀L⟩ : L) = ⟨(π₀ : PadicAlgCl q), hπ₀L⟩
    exact (hK' ⟨(π₀ : PadicAlgCl q), hπ₀L⟩).1 π₀.2 s hs
  ·
    exact hπ₀lt
  ·
    intro y hy hylt
    show ‖(y : PadicAlgCl q)‖ ≤ ‖((π₀ : K') : PadicAlgCl q)‖
    have hyE := hstar y hy
    by_cases hy0 : (y : PadicAlgCl q) = 0
    · rw [hy0, norm_zero]; exact norm_nonneg _
    · have hyE0 : (⟨(y : PadicAlgCl q), hyE⟩ :
          IntermediateField.adjoin K' {ζ : PadicAlgCl q | ζ ^ (q ^ N₀ - 1) = 1}) ≠ 0 :=
        fun h => hy0 (congrArg Subtype.val h)
      obtain ⟨y', hy'⟩ := IntermediateField.exists_norm_eq_adjoin_rootsOfUnity_padic q K' N₀ hN₀ ⟨(y : PadicAlgCl q), hyE⟩ hyE0
      have hy'0 : y' ≠ 0 := by
        intro h
        apply hy0
        rw [h] at hy'
        have : ‖(y : PadicAlgCl q)‖ = 0 := by simpa using hy'
        rwa [norm_eq_zero] at this
      obtain ⟨i, hi⟩ := hπ₀val y' hy'0
      change ‖(y : PadicAlgCl q)‖ = _ at hy'
      rw [hy', hi] at hylt ⊢
      have hi1 : 0 < i := (zpow_lt_one_iff_right_of_lt_one₀ hπ₀pos hπ₀lt).1 hylt
      have := zpow_le_zpow_right_of_le_one₀ hπ₀pos hπ₀lt.le (show (1 : ℤ) ≤ i from hi1)
      rwa [zpow_one] at this

end S_ExtCitation_LocalLevel_exists_frobenius_uniformiser_inf_level
end P2MW
export P2MW.S_ExtCitation_LocalLevel_exists_frobenius_uniformiser_inf_level (solution)
