-- Prove2me | solution 1 for ExtCitation.exists_tame_generator_at_level_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/e3a92d47-5bcb-54d3-92ee-729ba0397b2f

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ExtCitation_InertiaKummerCharacter
import Theorems.Thm_ExtCitation_exists_tame_generator_at_level
import Theorems.Thm_ExtCitation_LocalLevel_dvd_of_forall_inertia_apply_pow_eq
import Theorems.Thm_ExtCitation_LocalLevel_exists_level_frobenius_pow_dvd_and_apply_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_exists_tame_generator_at_level_of_dvd
p2m_attr_erase "instance" "ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "ExtCitation.LocalLevel.coe_smul_OO"

set_option autoImplicit false

open ExtCitation

namespace P2mS17LC

variable (q : Nat.Primes)

noncomputable abbrev G : Type := primeLocalGaloisGroup q
noncomputable abbrev r : G q →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) := primeLocalToGlobal q
noncomputable abbrev I : Subgroup (G q) := ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)
noncomputable abbrev U (F : IntermediateField ℚ (AlgebraicClosure ℚ)) : Subgroup (G q) :=
  (F.fixingSubgroup).comap (primeLocalToGlobal q)

scoped instance normal_I : (I q).Normal := by
  have : I q = ((primeLocalPlace q).inertiaSubgroup ℚ).comap (toDecomp q) := by
    ext g
    rw [Subgroup.mem_comap, Subgroup.mem_comap, ValuationSubring.inertiaSubgroupIn, Subgroup.mem_map]
    constructor
    · rintro ⟨τ, hτ, hτg⟩
      have : toDecomp q g = τ := Subtype.ext hτg.symm
      rwa [this]
    · intro h; exact ⟨toDecomp q g, h, rfl⟩
  rw [this, ValuationSubring.inertiaSubgroup, MonoidHom.comap_ker]
  exact MonoidHom.normal_ker _

section Level

variable (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] [IsGalois ℚ F]

noncomputable def ρ : G q →* (F ≃ₐ[ℚ] F) := (AlgEquiv.restrictNormalHom F).comp (primeLocalToGlobal q)

theorem U_eq_ker : U q F = (ρ q F).ker := by
  ext g
  rw [Subgroup.mem_comap, IntermediateField.mem_fixingSubgroup_iff, MonoidHom.mem_ker, ρ, MonoidHom.comp_apply,
    AlgEquiv.ext_iff]
  constructor
  · intro h x
    apply Subtype.ext
    exact (AlgEquiv.restrictNormal_commutes (primeLocalToGlobal q g) F x).trans (h x x.2)
  · intro h x hx
    exact (AlgEquiv.restrictNormal_commutes (primeLocalToGlobal q g) F ⟨x, hx⟩).symm.trans
      (congrArg Subtype.val (h ⟨x, hx⟩))

scoped instance normal_U : (U q F).Normal := by rw [U_eq_ker]; exact MonoidHom.normal_ker _

scoped instance normal_IU : (I q ⊔ U q F).Normal := by
  refine ⟨fun h hh g => ?_⟩
  let C : Subgroup (G q) := (I q ⊔ U q F).comap (MulAut.conj g).toMonoidHom
  have h1 : I q ≤ C := fun i hi => Subgroup.mem_comap.mpr (Subgroup.mem_sup_left ((normal_I q).conj_mem i hi g))
  have h2 : U q F ≤ C := fun u hu => Subgroup.mem_comap.mpr (Subgroup.mem_sup_right ((normal_U q F).conj_mem u hu g))
  exact (sup_le h1 h2) hh

theorem exists_pow_mem_U (g : G q) : ∃ N : ℕ, 0 < N ∧ g ^ N ∈ U q F := by
  refine ⟨orderOf (ρ q F g), orderOf_pos (ρ q F g), ?_⟩
  rw [U_eq_ker, MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]

end Level

theorem pow_apply_eq {g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} {ζ α : AlgebraicClosure ℚ} {c : ℕ}
    (hgζ : g ζ = ζ) (hgα : g α = ζ ^ c * α) (a : ℕ) : (g ^ a) α = ζ ^ (a * c) * α := by
  induction a with
  | zero => rw [pow_zero, AlgEquiv.one_apply, zero_mul, pow_zero, one_mul]
  | succ a ih =>
    have hζa : (g ^ a) ζ = ζ := by
      clear ih
      induction a with
      | zero => rw [pow_zero, AlgEquiv.one_apply]
      | succ a ih => rw [pow_succ, AlgEquiv.mul_apply, hgζ, ih]
    rw [pow_succ, AlgEquiv.mul_apply, hgα, map_mul, map_pow, hζa, ih, ← mul_assoc, ← pow_add, Nat.succ_mul,
      add_comm]

theorem exists_apply_eq_pow_mul {g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} {ζ α : AlgebraicClosure ℚ} {n : ℕ}
    (hζ : IsPrimitiveRoot ζ n) (hα : α ^ n = ((q : ℕ) : AlgebraicClosure ℚ)) (hα0 : α ≠ 0) :
    ∃ c : ℕ, g α = ζ ^ c * α := by
  haveI : NeZero n := ⟨fun h0 => by
    rw [h0, pow_zero] at hα
    exact absurd hα.symm (by exact_mod_cast q.2.one_lt.ne')⟩
  have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.2.ne_zero
  have h1 : (g α * α⁻¹) ^ n = 1 := by
    rw [mul_pow, ← map_pow, hα, map_natCast, inv_pow, hα, mul_inv_cancel₀ hq0]
  obtain ⟨c, -, hζc⟩ := hζ.eq_pow_of_pow_eq_one h1
  exact ⟨c, by rw [hζc, inv_mul_cancel_right₀ hα0]⟩

end P2mS17LC
p2m_reactivate "P2MW.S_ExtCitation_exists_tame_generator_at_level_of_dvd.P2mS17LC"

open P2mS17LC in
theorem solution (q : Nat.Primes)
    (φ : primeLocalGaloisGroup q) (hφ : (primeLocalPlace q).IsFrobeniusAt (primeLocalToGlobal q φ) q)
    (F₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F₀]
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d) (hqn : ¬ (q : ℕ) ∣ n) :
    ∃ (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ F) (_ : IsGalois ℚ F),
      F₀ ≤ F ∧
      ∃ (t : primeLocalGaloisGroup q) (W : Subgroup (primeLocalGaloisGroup q)) (_ : W.Normal),
        t ∈ ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q) ∧
        (F.fixingSubgroup).comap (primeLocalToGlobal q) ≤ W ∧
        W ≤ ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q) ⊔
              (F.fixingSubgroup).comap (primeLocalToGlobal q) ∧
        (∀ w ∈ W, ∃ a : ℕ, w ^ ((q : ℕ) ^ a) ∈ (F.fixingSubgroup).comap (primeLocalToGlobal q)) ∧
        (∀ i ∈ ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q), ∃ a : ℕ, (t ^ a)⁻¹ * i ∈ W) ∧
        (t ^ (q : ℕ))⁻¹ * (φ * t * φ⁻¹) ∈ W ∧
        IsOfFinOrder (QuotientGroup.mk t : primeLocalGaloisGroup q ⧸ W) ∧
        n ∣ orderOf (QuotientGroup.mk t : primeLocalGaloisGroup q ⧸ W) ∧
        ∃ (_ : (Subgroup.zpowers (QuotientGroup.mk t : primeLocalGaloisGroup q ⧸ W)).Normal),
          d ∣ orderOf (QuotientGroup.mk (QuotientGroup.mk φ : primeLocalGaloisGroup q ⧸ W) :
                (primeLocalGaloisGroup q ⧸ W) ⧸ Subgroup.zpowers (QuotientGroup.mk t : primeLocalGaloisGroup q ⧸ W)) ∧
          ∃ j : ℕ, n ∣ j ∧
            (QuotientGroup.mk φ : primeLocalGaloisGroup q ⧸ W) ^
                orderOf (QuotientGroup.mk (QuotientGroup.mk φ : primeLocalGaloisGroup q ⧸ W) :
                  (primeLocalGaloisGroup q ⧸ W) ⧸ Subgroup.zpowers (QuotientGroup.mk t : primeLocalGaloisGroup q ⧸ W))
              = (QuotientGroup.mk t : primeLocalGaloisGroup q ⧸ W) ^ j := by
  classical
  haveI : Fact (q : ℕ).Prime := ⟨q.2⟩
  have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.2.ne_zero

  haveI : NeZero ((n : ℕ) : AlgebraicClosure ℚ) := ⟨Nat.cast_ne_zero.mpr hn.ne'⟩
  haveI : NeZero ((n : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hn.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) n
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq ((q : ℕ) : AlgebraicClosure ℚ) hn
  have hα0 : α ≠ 0 := by rintro rfl; rw [zero_pow hn.ne'] at hα; exact hq0 hα.symm
  have hcop : Nat.Coprime n q := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd q.2).mpr hqn)

  obtain ⟨F, hF₀, hFfd, hFgal, hζF, hαF, hB⟩ :=
    ExtCitation.LocalLevel.exists_level_frobenius_pow_dvd_and_apply_eq q φ hφ F₀ n d hn hd hqn hζ hα
  haveI := hFfd; haveI := hFgal
  obtain ⟨t, W, ht, hUW, hWH, hWn, hWq, hgen, hrel⟩ := exists_tame_generator_at_level q φ hφ F
  haveI := hWn

  obtain ⟨N₀, hN₀, htN₀⟩ := exists_pow_mem_U q F t
  have hfin : IsOfFinOrder (QuotientGroup.mk t : G q ⧸ W) :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨N₀, hN₀, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hUW htN₀⟩

  have hTeq : Subgroup.zpowers (QuotientGroup.mk t : G q ⧸ W) = (I q ⊔ U q F).map (QuotientGroup.mk' W) := by
    apply le_antisymm
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_map.mpr ⟨t, Subgroup.mem_sup_left ht, rfl⟩
    · rw [Subgroup.map_le_iff_le_comap]
      refine sup_le (fun i hi => ?_) (fun u hu => ?_)
      · obtain ⟨a, ha⟩ := hgen i hi
        rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, ← QuotientGroup.eq.mpr ha, QuotientGroup.mk_pow]
        exact Subgroup.npow_mem_zpowers _ a
      · rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff u).mpr (hUW hu)]
        exact one_mem _
  have hTmem : ∀ x : G q, (QuotientGroup.mk x : G q ⧸ W) ∈ Subgroup.zpowers (QuotientGroup.mk t : G q ⧸ W) ↔ x ∈ I q ⊔ U q F := by
    intro x
    rw [hTeq, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq] at hyx
      have : x = y * (y⁻¹ * x) := (mul_inv_cancel_left _ _).symm
      rw [this]
      exact mul_mem hy (hWH hyx)
    · intro hx; exact ⟨x, hx, rfl⟩
  have hTn : (Subgroup.zpowers (QuotientGroup.mk t : G q ⧸ W)).Normal := by
    rw [hTeq]; exact Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective W)

  have hWζ : ∀ w ∈ W, r q w ζ = ζ := by
    intro w hw
    have hw' := hWH hw
    let S : Subgroup (G q) := (MulAction.stabilizer (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ζ).comap (r q)
    have h1 : I q ≤ S := fun i hi => inertiaPullback_smul_eq_of_pow_eq_one q hi hqn hζ.pow_eq_one
    have h2 : U q F ≤ S := fun u hu => (IntermediateField.mem_fixingSubgroup_iff _ _).mp (Subgroup.mem_comap.mp hu) ζ hζF
    exact (sup_le h1 h2) hw'
  have hWα : ∀ w ∈ W, r q w α = α := by
    intro w hw
    obtain ⟨a, ha⟩ := hWq w hw
    obtain ⟨c, hc⟩ := exists_apply_eq_pow_mul q (g := r q w) hζ hα hα0
    have h1 : (r q w ^ ((q : ℕ) ^ a)) α = α := by
      rw [← map_pow]; exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp (Subgroup.mem_comap.mp ha) α hαF
    rw [pow_apply_eq (hWζ w hw) hc] at h1
    have h2 : ζ ^ ((q : ℕ) ^ a * c) = 1 := by
      have := mul_right_cancel₀ hα0 (h1.trans (one_mul α).symm)
      exact this
    rw [hζ.pow_eq_one_iff_dvd] at h2
    have h3 : n ∣ c := (Nat.Coprime.pow_right a hcop).dvd_of_dvd_mul_left h2
    rw [hc, (hζ.pow_eq_one_iff_dvd c).mpr h3, one_mul]
  have htζ : r q t ζ = ζ := inertiaPullback_smul_eq_of_pow_eq_one q ht hqn hζ.pow_eq_one
  obtain ⟨c₀, hc₀⟩ := exists_apply_eq_pow_mul q (g := r q t) hζ hα hα0

  have hkey : ∀ M : ℕ, ζ ^ (M * c₀) = 1 → ∀ i ∈ I q, r q i (α ^ M) = α ^ M := by
    intro M hM i hi
    obtain ⟨a, ha⟩ := hgen i hi
    have hi' : i = t ^ a * ((t ^ a)⁻¹ * i) := (mul_inv_cancel_left _ _).symm
    rw [hi', map_mul, AlgEquiv.mul_apply, map_pow (r q ((t ^ a)⁻¹ * i)) α M, hWα _ ha, map_pow (r q) t a,
      map_pow ((r q t) ^ a) α M, pow_apply_eq htζ hc₀ a, mul_pow, ← pow_mul,
      show a * c₀ * M = M * c₀ * a by ring, pow_mul, hM, one_pow, one_mul]
  refine ⟨F, hFfd, hFgal, hF₀, t, W, hWn, ht, hUW, hWH, hWq, hgen, hrel, hfin, ?_, hTn, ?_, ?_⟩
  ·
    set N := orderOf (QuotientGroup.mk t : G q ⧸ W) with hNdef
    have htN : t ^ N ∈ W := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]; exact pow_orderOf_eq_one _
    refine ExtCitation.LocalLevel.dvd_of_forall_inertia_apply_pow_eq q hn hqn hα N (hkey N ?_)
    have h1 := hWα _ htN
    rw [map_pow, pow_apply_eq htζ hc₀ N] at h1
    exact mul_right_cancel₀ hα0 (h1.trans (one_mul α).symm)
  ·
    set f := orderOf (QuotientGroup.mk (QuotientGroup.mk φ : G q ⧸ W) : (G q ⧸ W) ⧸ Subgroup.zpowers (QuotientGroup.mk t : G q ⧸ W))
    have hφf : φ ^ f ∈ I q ⊔ U q F := by
      rw [← hTmem, QuotientGroup.mk_pow, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact pow_orderOf_eq_one _
    exact (dvd_mul_left d n).trans (hB f hφf).1
  ·
    set f := orderOf (QuotientGroup.mk (QuotientGroup.mk φ : G q ⧸ W) : (G q ⧸ W) ⧸ Subgroup.zpowers (QuotientGroup.mk t : G q ⧸ W))
    have hφfT : (QuotientGroup.mk (φ ^ f) : G q ⧸ W) ∈ Subgroup.zpowers (QuotientGroup.mk t : G q ⧸ W) := by
      rw [QuotientGroup.mk_pow, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]; exact pow_orderOf_eq_one _
    have hφf : φ ^ f ∈ I q ⊔ U q F := (hTmem _).mp hφfT
    obtain ⟨j, hj⟩ := (hfin.mem_powers_iff_mem_zpowers).mpr hφfT
    have hjW : (t ^ j)⁻¹ * φ ^ f ∈ W := by
      rw [← QuotientGroup.eq, QuotientGroup.mk_pow]; exact hj
    refine ⟨j, ?_, by rw [← QuotientGroup.mk_pow W φ f, ← hj]⟩
    refine ExtCitation.LocalLevel.dvd_of_forall_inertia_apply_pow_eq q hn hqn hα j (hkey j ?_)
    have h1 : r q (φ ^ f) α = α := (hB f hφf).2
    have h2 : φ ^ f = t ^ j * ((t ^ j)⁻¹ * φ ^ f) := (mul_inv_cancel_left _ _).symm
    rw [h2, map_mul, AlgEquiv.mul_apply, hWα _ hjW, map_pow, pow_apply_eq htζ hc₀ j] at h1
    exact mul_right_cancel₀ hα0 (h1.trans (one_mul α).symm)

end S_ExtCitation_exists_tame_generator_at_level_of_dvd
end P2MW
export P2MW.S_ExtCitation_exists_tame_generator_at_level_of_dvd (solution)
