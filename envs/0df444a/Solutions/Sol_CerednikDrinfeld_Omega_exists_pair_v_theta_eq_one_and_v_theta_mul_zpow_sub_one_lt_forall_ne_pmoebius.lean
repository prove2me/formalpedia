-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_pair_v_theta_eq_one_and_v_theta_mul_zpow_sub_one_lt_forall_ne_pmoebius
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/9c8cf680-8ae1-514c-8463-e94fd50a777e

import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_CerednikDrinfeld_OmegaTubes
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Theorems.Thm_CerednikDrinfeld_Omega_v_apply_smul_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq_of_isUnit_of_eq_theta
import Theorems.Thm_CerednikDrinfeld_Omega_theta_pmoebius_mul_theta_eq_theta
import Theorems.Thm_CerednikDrinfeld_Omega_thetaMultipliable_of_isDiscrete_of_isExhausted
import Theorems.Thm_CerednikDrinfeld_Omega_exists_isUnit_coe_eq_thetaMer_apply_smul_eq_period_mul
import Theorems.Thm_CerednikDrinfeld_Omega_isDiscrete_of_finite_stabilizer_stdVertex
import Theorems.Thm_CerednikDrinfeld_Omega_finite_setOf_pmoebius_mem_affinoid
import Theorems.Thm_CerednikDrinfeld_Omega_exists_v_apply_div_sub_one_lt_of_isUnit_of_mem_stdEdgeTube
import Theorems.Thm_CerednikDrinfeld_Omega_v_apply_eq_and_v_apply_eq_mul_zpow_of_isUnit_of_forall_mem_stdEdgeTube
import Theorems.Thm_CerednikDrinfeld_Omega_holRing_eq_and_affinoid_zero_eq
import Theorems.Thm_CerednikDrinfeld_BruhatTits_exists_smul_stdVertex_eq_fst_and_mul_smul_stdVertex_eq_snd
import Theorems.Thm_CerednikDrinfeld_BruhatTits_adj_stdVertex_iff_eq_smul_of_uniformizer
import Theorems.Thm_CerednikDrinfeld_Omega_crossRatio_self
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_pair_v_theta_eq_one_and_v_theta_mul_zpow_sub_one_lt_forall_ne_pmoebius
p2m_attr_erase "simp" "LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq CerednikDrinfeld.Mumford.walkOverlap_nil_right CerednikDrinfeld.Mumford.walkOverlap_nil_left LocalGL2.swapUnit_val"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped MatrixGroups
p2m_open "CerednikDrinfeld CerednikDrinfeld.Omega~theta_self_eq_one CerednikDrinfeld.Mumford MulAction"

noncomputable section

namespace UAP

section PUTree

variable {R K₀ : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
  [IsFractionRing R K₀] {ϖ : R}
  {K : Type} [Field K] [Algebra K₀ K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem v_algebraMap_units_eq_one
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1) (u : Rˣ) :
    Valued.v (algebraMap K₀ K (algebraMap R K₀ (u : R))) = 1 := by
  apply le_antisymm (hint u)
  have h1 : algebraMap K₀ K (algebraMap R K₀ (u : R)) * algebraMap K₀ K (algebraMap R K₀ (↑u⁻¹ : R)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  calc (1 : Γ₀) = Valued.v (algebraMap K₀ K (algebraMap R K₀ (u : R))) *
        Valued.v (algebraMap K₀ K (algebraMap R K₀ (↑u⁻¹ : R))) := by rw [← Valuation.map_mul, h1, Valuation.map_one]
    _ ≤ Valued.v (algebraMap K₀ K (algebraMap R K₀ (u : R))) * 1 := mul_le_mul_right (hint _) _
    _ = _ := mul_one _

theorem algebraMap_ne_zero_of_irreducible (hϖ : Irreducible ϖ) : algebraMap R K₀ ϖ ≠ 0 := fun h =>
  hϖ.ne_zero ((IsFractionRing.to_map_eq_zero_iff (K := K₀)).mp h)

theorem v_algebraMap_pos (hϖ : Irreducible ϖ) : 0 < Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) :=
  lt_of_le_of_ne zero_le' (Ne.symm ((Valuation.ne_zero_iff _).mpr
    ((map_ne_zero _).mpr (algebraMap_ne_zero_of_irreducible hϖ))))

theorem v_algebraMap_lt_one (hϖ : Irreducible ϖ)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a) :
    Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) < 1 := by
  by_contra h
  rw [not_lt] at h
  have hϖ0 := algebraMap_ne_zero_of_irreducible (K₀ := K₀) hϖ
  have hle : Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)⁻¹) ≤ 1 := by
    rw [map_inv₀, Valuation.map_inv, inv_le_one₀ (v_algebraMap_pos hϖ)]
    exact h
  obtain ⟨b, hb⟩ := hv _ hle
  apply hϖ.not_isUnit
  refine isUnit_iff_exists_inv.mpr ⟨b, ?_⟩
  apply IsFractionRing.injective R K₀
  rw [map_mul, hb, map_one, mul_inv_cancel₀ hϖ0]

theorem exists_v_algebraMap_eq_zpow (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1) (a : K₀) (ha : a ≠ 0) :
    ∃ k : ℤ, Valued.v (algebraMap K₀ K a) = Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ k := by
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hϖ ha
  refine ⟨k, ?_⟩
  rw [Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀, Valuation.map_mul, map_zpow₀,
    v_algebraMap_units_eq_one hint, one_mul]

theorem v_algebraMap_le_or_one_le (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a) (a : K₀) :
    Valued.v (algebraMap K₀ K a) ≤ Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ∨
      1 ≤ Valued.v (algebraMap K₀ K a) := by
  by_cases ha : a = 0
  · left; rw [ha, map_zero, Valuation.map_zero]; exact zero_le'
  obtain ⟨k, hk⟩ := exists_v_algebraMap_eq_zpow hϖ hint a ha
  rw [hk]
  have h0 := v_algebraMap_pos (K₀ := K₀) (K := K) hϖ
  have h1 := (v_algebraMap_lt_one hϖ hv).le
  rcases le_or_gt k 0 with hk0 | hk0
  · exact Or.inr (one_le_zpow_of_nonpos₀ h0 h1 hk0)
  · left
    calc Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ k
        ≤ Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ (1 : ℤ) := zpow_le_zpow_right_of_le_one₀ h0 h1 (by omega)
      _ = _ := zpow_one _

theorem exists_pow_le_v_algebraMap_le (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a) (a : K₀) (ha : a ≠ 0) :
    ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ Valued.v (algebraMap K₀ K a) ∧
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)))⁻¹ ^ N := by
  obtain ⟨k, hk⟩ := exists_v_algebraMap_eq_zpow hϖ hint a ha
  have h0 := v_algebraMap_pos (K₀ := K₀) (K := K) hϖ
  have h1 := (v_algebraMap_lt_one hϖ hv).le
  refine ⟨k.natAbs, ?_, ?_⟩
  · rw [hk, ← zpow_natCast]
    exact zpow_le_zpow_right_of_le_one₀ h0 h1 (Int.le_natAbs)
  · rw [hk, inv_pow, ← zpow_natCast, ← zpow_neg]
    exact zpow_le_zpow_right_of_le_one₀ h0 h1 (by rw [Int.natCast_natAbs]; exact neg_abs_le k)

def treePseudoUniformizer (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a) :
    PseudoUniformizer K₀ K where
  ϖ := algebraMap R K₀ ϖ
  pos := v_algebraMap_pos hϖ
  lt_one := v_algebraMap_lt_one hϖ hv
  scale := exists_pow_le_v_algebraMap_le hϖ hint hv

@[scoped simp] theorem treePseudoUniformizer_ϖ (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a) :
    (treePseudoUniformizer hϖ hint hv).ϖ = algebraMap R K₀ ϖ := rfl

theorem dvd_of_v_algebraMap_lt_one (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a) (d : R)
    (hd : Valued.v (algebraMap K₀ K (algebraMap R K₀ d)) < 1) : ϖ ∣ d := by
  have hϖ0 := algebraMap_ne_zero_of_irreducible (K₀ := K₀) hϖ
  have h0 := v_algebraMap_pos (K₀ := K₀) (K := K) hϖ
  have hle : Valued.v (algebraMap K₀ K (algebraMap R K₀ d)) ≤ Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) := by
    rcases v_algebraMap_le_or_one_le hϖ hint hv (algebraMap R K₀ d) with h | h
    · exact h
    · exact absurd hd (not_lt.mpr h)
  have hint' : Valued.v (algebraMap K₀ K (algebraMap R K₀ d / algebraMap R K₀ ϖ)) ≤ 1 := by
    rw [map_div₀, Valuation.map_div, div_le_one₀ h0]
    exact hle
  obtain ⟨c, hc⟩ := hv _ hint'
  refine ⟨c, ?_⟩
  apply IsFractionRing.injective R K₀
  rw [map_mul, hc, mul_div_cancel₀ _ hϖ0]

theorem exists_finset_residue_representatives (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a) :
    ∃ T : Finset K₀, (∀ t ∈ T, Valued.v (algebraMap K₀ K t) ≤ 1) ∧
      (∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < 1) ∧
      (∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → 1 ≤ Valued.v (algebraMap K₀ K t - algebraMap K₀ K t')) := by
  classical
  haveI : Fintype (R ⧸ Ideal.span {ϖ}) := Fintype.ofFinite _
  set σ : R ⧸ Ideal.span {ϖ} → R := Function.surjInv (Ideal.Quotient.mk_surjective (I := Ideal.span {ϖ})) with hσ
  have hσmk : ∀ q, Ideal.Quotient.mk (Ideal.span {ϖ}) (σ q) = q :=
    Function.surjInv_eq (Ideal.Quotient.mk_surjective (I := Ideal.span {ϖ}))
  refine ⟨Finset.univ.image (fun q => algebraMap R K₀ (σ q)), ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp ht
    exact hint _
  · intro a ha
    obtain ⟨b, hb⟩ := hv a ha
    refine ⟨algebraMap R K₀ (σ (Ideal.Quotient.mk _ b)), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    have hmem : b - σ (Ideal.Quotient.mk _ b) ∈ Ideal.span {ϖ} := by
      rw [← Ideal.Quotient.eq, hσmk]
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton.mp hmem
    rw [← hb, ← map_sub, ← map_sub, he, map_mul, map_mul, Valuation.map_mul]
    calc Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) * Valued.v (algebraMap K₀ K (algebraMap R K₀ e))
        ≤ Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) * 1 := mul_le_mul_right (hint e) _
      _ < 1 := by rw [mul_one]; exact v_algebraMap_lt_one hϖ hv
  · intro t ht t' ht' hne
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.mp ht'
    have hqq : q ≠ q' := fun h => hne (by rw [h])
    by_contra hlt
    rw [not_le] at hlt
    rw [← map_sub, ← map_sub] at hlt
    have hdvd := dvd_of_v_algebraMap_lt_one hϖ hint hv _ hlt
    apply hqq
    rw [← hσmk q, ← hσmk q', Ideal.Quotient.eq]
    exact Ideal.mem_span_singleton.mpr hdvd

end PUTree

end UAP
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_exists_pair_v_theta_eq_one_and_v_theta_mul_zpow_sub_one_lt_forall_ne_pmoebius.UAP"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_exists_pair_v_theta_eq_one_and_v_theta_mul_zpow_sub_one_lt_forall_ne_pmoebius.UAP"

namespace BetaGlue

p2m_open "CerednikDrinfeld.Omega~theta_self_eq_one"

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem exists_isUnit_coe_eq (Q P : PseudoUniformizer K₀ K) (U : ↥(holRing Q)) (hU : IsUnit U) :
    ∃ U' : ↥(holRing P), IsUnit U' ∧ (U' : ↥(upperHalfPlane K₀ K) → K) = (U : ↥(upperHalfPlane K₀ K) → K) := by
  have h := (CerednikDrinfeld.Omega.holRing_eq_and_affinoid_zero_eq Q P).1
  obtain ⟨V, hUV⟩ := hU.exists_right_inv
  have hval : (U : ↥(upperHalfPlane K₀ K) → K) * (V : ↥(upperHalfPlane K₀ K) → K) = 1 := by
    have := congrArg Subtype.val hUV
    exact this
  refine ⟨⟨U.1, h ▸ U.2⟩, IsUnit.of_mul_eq_one (b := ⟨V.1, h ▸ V.2⟩) (Subtype.ext hval), rfl⟩

theorem stdEdgeTube_subset_affinoid_one (P : PseudoUniformizer K₀ K)
    (hunif : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ Valued.v (algebraMap K₀ K P.ϖ) ∨ 1 ≤ Valued.v (algebraMap K₀ K a)) :
    stdEdgeTube P ⊆ affinoid P 1 := by
  rintro z ⟨hz, h1, h2⟩
  rw [mem_affinoid_iff', pow_one, pow_one]
  have hr1 : Valued.v (algebraMap K₀ K P.ϖ) < 1 := P.lt_one
  refine ⟨h2.le.trans ((one_lt_inv₀ P.pos).2 hr1).le, fun a => ?_⟩
  rcases hunif a with h | h
  · rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_left _ (by rw [Valuation.map_neg]; exact lt_of_le_of_lt h h1)]
    exact h1.le
  · rw [sub_eq_neg_add, Valuation.map_add_eq_of_lt_left _ (by rw [Valuation.map_neg]; exact lt_of_lt_of_le h2 h), Valuation.map_neg]
    exact hr1.le.trans h

theorem exists_mem_stdEdgeTube_not_mem [IsAlgClosed K] (P : PseudoUniformizer K₀ K)
    (hunif : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ Valued.v (algebraMap K₀ K P.ϖ) ∨ 1 ≤ Valued.v (algebraMap K₀ K a))
    (ζ : K) (hζ : Valued.v ζ = 1) (F : Set K) (hF : F.Finite) :
    ∃ x : K, x ∈ stdEdgeTube P ∧ x ∉ F ∧ ζ * x ∉ F := by
  classical
  set π : K := algebraMap K₀ K P.ϖ with hπ
  have hr0 : Valued.v π ≠ 0 := P.pos.ne'
  have hr1 : Valued.v π < 1 := P.lt_one
  have hπ0 : π ≠ 0 := (Valuation.ne_zero_iff _).mp hr0
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq π (by norm_num : 0 < 2)
  have hvs : Valued.v s ^ 2 = Valued.v π := by rw [← map_pow, hs]
  have hs0 : Valued.v s ≠ 0 := fun h => by rw [h, zero_pow two_ne_zero] at hvs; exact hr0 hvs.symm
  have hs1 : Valued.v s < 1 := by
    by_contra h
    have : 1 ≤ Valued.v s ^ 2 := one_le_pow₀ (not_lt.mp h)
    rw [hvs] at this
    exact absurd hr1 (not_lt.mpr this)
  have hrs : Valued.v π < Valued.v s := by
    rw [← hvs, pow_two]
    refine lt_of_le_of_ne ?_ ?_
    · calc Valued.v s * Valued.v s ≤ Valued.v s * 1 := mul_le_mul_right hs1.le _
        _ = Valued.v s := mul_one _
    · intro h
      have h' : Valued.v s * Valued.v s = Valued.v s * 1 := by rw [mul_one]; exact h
      exact absurd hs1 (by rw [mul_left_cancel₀ hs0 h']; exact lt_irrefl 1)

  set x : ℕ → K := fun k => s * (1 + π ^ (k + 1)) with hx
  have hvx : ∀ k, Valued.v (x k) = Valued.v s := by
    intro k
    rw [hx]; dsimp only
    have hsmall : Valued.v (π ^ (k + 1)) < Valued.v (1 : K) := by
      rw [Valuation.map_pow, Valuation.map_one, pow_succ]
      calc Valued.v π ^ k * Valued.v π ≤ 1 * Valued.v π := mul_le_mul_left (pow_le_one₀ zero_le' hr1.le) _
        _ = Valued.v π := one_mul _
        _ < 1 := hr1
    rw [Valuation.map_mul, Valuation.map_add_eq_of_lt_left _ hsmall, Valuation.map_one, mul_one]
  have hxinj : Function.Injective x := by
    intro k k' h
    rw [hx] at h
    have hs' : s ≠ 0 := (Valuation.ne_zero_iff _).mp hs0
    have h2 : π ^ (k + 1) = π ^ (k' + 1) := by
      have := mul_left_cancel₀ hs' h
      exact add_left_cancel this
    have h3 : Valued.v π ^ (k + 1) = Valued.v π ^ (k' + 1) := by rw [← Valuation.map_pow, ← Valuation.map_pow, h2]
    have := pow_right_injective₀ P.pos hr1.ne h3
    omega
  have hζ0 : ζ ≠ 0 := (Valuation.ne_zero_iff _).mp (by rw [hζ]; exact one_ne_zero)
  have hbad : {k : ℕ | x k ∈ F ∨ ζ * x k ∈ F}.Finite := by
    refine Set.Finite.subset ((hF.preimage hxinj.injOn).union (hF.preimage ((mul_right_injective₀ hζ0).comp hxinj).injOn)) ?_
    rintro k (h | h)
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨k, -, hk⟩ := Set.Infinite.exists_notMem_finite (Set.infinite_univ (α := ℕ)) hbad
  simp only [Set.mem_setOf_eq, not_or] at hk
  refine ⟨x k, ⟨?_, ?_, ?_⟩, hk.1, hk.2⟩
  · rw [mem_upperHalfPlane_iff]
    rintro a ha
    rcases hunif a with h | h
    · exact absurd (hrs.trans_le (le_of_eq (hvx k).symm)) (by rw [← ha]; exact not_lt.mpr h)
    · exact absurd (lt_of_le_of_lt (le_of_eq (hvx k)) hs1) (by rw [← ha]; exact not_lt.mpr h)
  · rw [hvx]; exact hrs
  · rw [hvx]; exact hs1

end BetaGlue
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_exists_pair_v_theta_eq_one_and_v_theta_mul_zpow_sub_one_lt_forall_ne_pmoebius.UAP"

namespace EdgePairResidue

theorem S1_isDiscrete
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (K : Type) [Field K] [Algebra K₀ K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ ε)
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀))
    [MulAction G (LT.LatticeTree.Vertex R K₀)]
    (hρ : CerednikDrinfeld.Mumford.ActsThrough (LT.LatticeTree.Vertex R K₀) ρ)
    (hfin : ∀ w : LT.LatticeTree.Vertex R K₀, Finite (MulAction.stabilizer G w)) :
    CerednikDrinfeld.Omega.IsDiscrete K ρ := by
  haveI := hfin (LT.LatticeTree.stdVertex R K₀)
  refine CerednikDrinfeld.Omega.isDiscrete_of_finite_stabilizer_stdVertex R K₀ ϖ hϖ K hint hv hq ρ ?_
  refine (Set.toFinite (MulAction.stabilizer G (LT.LatticeTree.stdVertex R K₀) : Set G)).subset fun γ hγ => ?_
  rw [Set.mem_setOf_eq] at hγ
  show γ • LT.LatticeTree.stdVertex R K₀ = LT.LatticeTree.stdVertex R K₀
  rw [hρ γ]; exact hγ

section PU
variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem v_eq_one_of_pu {x : K} (hx : Valued.v (x - 1) < 1) : Valued.v x = 1 := by
  have : x = 1 + (x - 1) := by ring
  rw [this, Valuation.map_one_add_of_lt _ hx]

theorem pu_mul {x y : K} (hx : Valued.v (x - 1) < 1) (hy : Valued.v (y - 1) < 1) : Valued.v (x * y - 1) < 1 := by
  have : x * y - 1 = x * (y - 1) + (x - 1) := by ring
  rw [this]
  refine Valuation.map_add_lt _ ?_ hx
  rw [map_mul, v_eq_one_of_pu hx, one_mul]
  exact hy

theorem pu_inv {x : K} (hx : Valued.v (x - 1) < 1) : Valued.v (x⁻¹ - 1) < 1 := by
  have hx1 := v_eq_one_of_pu hx
  have hx0 : x ≠ 0 := (Valuation.ne_zero_iff _).1 (by rw [hx1]; exact one_ne_zero)
  have : x⁻¹ - 1 = -(x⁻¹ * (x - 1)) := by field_simp; ring
  rw [this, Valuation.map_neg, map_mul, map_inv₀, hx1, inv_one, one_mul]
  exact hx

theorem pu_final {θ c x ζ : K} {m : ℤ} (hc : c ≠ 0) (hx : x ≠ 0) (hζ : ζ ≠ 0)
    (h1 : Valued.v (1 / (c * x ^ m) - 1) < 1) (h2 : Valued.v (θ / (c * (ζ * x) ^ m) - 1) < 1) :
    Valued.v (θ * (ζ ^ m)⁻¹ - 1) < 1 := by
  have hxm : x ^ m ≠ 0 := zpow_ne_zero m hx
  have hζm : ζ ^ m ≠ 0 := zpow_ne_zero m hζ
  have h1' : Valued.v (c * x ^ m - 1) < 1 := by
    have := pu_inv h1; rwa [one_div, inv_inv] at this
  have key : θ * (ζ ^ m)⁻¹ = (θ / (c * (ζ * x) ^ m)) * (c * x ^ m) := by
    rw [mul_zpow]; field_simp
  rw [key]
  exact pu_mul h2 h1'

end PU
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_exists_pair_v_theta_eq_one_and_v_theta_mul_zpow_sub_one_lt_forall_ne_pmoebius.UAP"

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem isExhausted_of_forall_exists_pow_le (ϖ₁ P : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ₁)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K P.ϖ) ^ N ≤ ε) : IsExhausted P := by
  intro z hz
  obtain ⟨n, hn⟩ := hex z hz
  rw [mem_affinoid_iff'] at hn
  obtain ⟨N, hN⟩ := hq (Valued.v (algebraMap K₀ K ϖ₁.ϖ) ^ n) (pow_ne_zero n ϖ₁.pos.ne')
  refine ⟨N, (mem_affinoid_iff' P N z).2 ⟨?_, fun a => hN.trans (hn.2 a)⟩⟩
  refine hn.1.trans ?_
  rw [inv_pow, inv_pow]
  exact (inv_le_inv₀ (pow_pos ϖ₁.pos n) (pow_pos P.pos N)).2 hN

theorem finite_pullback [DecidableEq K] (P : PseudoUniformizer K₀ K) (hexP : IsExhausted P)
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρd : IsDiscrete K ρ) (g : PGL(2, K₀))
    {y : K} (hy : y ∈ upperHalfPlane K₀ K) :
    {x : K | x ∈ affinoid P 1 ∧ ∃ γ : G, pmoebius K₀ (ρ γ) y = pmoebius K₀ g x}.Finite := by
  obtain ⟨N₁, hN₁⟩ := hexP y hy
  obtain ⟨N₂, hN₂⟩ := exists_mapsTo_affinoid P g 1
  have hyN : y ∈ affinoid P (N₁ + N₂) := affinoid_mono P (Nat.le_add_right N₁ N₂) hN₁
  have hB := CerednikDrinfeld.Omega.finite_setOf_pmoebius_mem_affinoid P ρ hρd (N₁ + N₂) hyN
  refine (hB.image fun γ => pmoebius K₀ g⁻¹ (pmoebius K₀ (ρ γ) y)).subset ?_
  rintro x ⟨hx, γ, hγ⟩
  refine ⟨γ, ?_, ?_⟩
  · show pmoebius K₀ (ρ γ) y ∈ affinoid P (N₁ + N₂)
    rw [hγ]
    exact affinoid_mono P (Nat.le_add_left N₂ N₁) (hN₂ hx)
  · show pmoebius K₀ g⁻¹ (pmoebius K₀ (ρ γ) y) = x
    rw [hγ, ← pmoebius_mul K₀ (affinoid_subset_upperHalfPlane P 1 hx), inv_mul_cancel, pmoebius_one]

theorem forall_pmoebius_ne_of_forall_ne [DecidableEq K] {G : Type} [Group G] (ρ : G →* PGL(2, K₀))
    {y a : K} (ha : a ∈ upperHalfPlane K₀ K) (h : ∀ γ : G, pmoebius K₀ (ρ γ) y ≠ a) :
    ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ y := by
  intro γ hγ
  apply h γ⁻¹
  rw [← hγ, ← pmoebius_mul K₀ ha, map_inv, inv_mul_cancel, pmoebius_one]

theorem mem_stdEdgeTube_of_v_eq (P : PseudoUniformizer K₀ K)
    (hunif : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ Valued.v (algebraMap K₀ K P.ϖ) ∨ 1 ≤ Valued.v (algebraMap K₀ K a))
    {x y : K} (hx : x ∈ stdEdgeTube P) (hxy : Valued.v y = Valued.v x) : y ∈ stdEdgeTube P := by
  obtain ⟨-, h1, h2⟩ := hx
  refine ⟨?_, by rw [hxy]; exact h1, by rw [hxy]; exact h2⟩
  rw [mem_upperHalfPlane_iff]
  intro a ha
  rcases hunif a with h | h
  · rw [ha, hxy] at h; exact absurd h1 (not_lt.2 h)
  · rw [ha, hxy] at h; exact absurd h2 (not_lt.2 h)

theorem exists_mem_affinoid_zero [IsAlgClosed K] (P : PseudoUniformizer K₀ K)
    (T : Finset K₀) (hT : ∀ t ∈ T, Valued.v (algebraMap K₀ K t) ≤ 1)
    (hTcov : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 →
      ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < 1) :
    ∃ w : K, w ∈ affinoid P 0 := by
  classical
  obtain ⟨t₀, ht₀, -⟩ := hTcov 0 (by rw [map_zero, Valuation.map_zero]; exact zero_le')
  have hcard : 0 < T.card := Finset.card_pos.2 ⟨t₀, ht₀⟩
  set ι : K₀ → K := fun t => algebraMap K₀ K t with hι
  set q : Polynomial K := ∏ t ∈ T, (Polynomial.X - Polynomial.C (ι t)) with hq
  have hqmon : q.Monic := Polynomial.monic_prod_of_monic _ _ fun t _ => Polynomial.monic_X_sub_C (ι t)
  have hqdeg : q.natDegree = T.card := by
    rw [hq, Polynomial.natDegree_prod_of_monic _ _ fun t _ => Polynomial.monic_X_sub_C (ι t)]
    simp
  have hqdeg' : 0 < q.degree := by
    rw [Polynomial.degree_eq_natDegree hqmon.ne_zero, hqdeg]; exact_mod_cast hcard
  have hpdeg : (q - Polynomial.C 1).degree ≠ 0 := by
    rw [Polynomial.degree_sub_C hqdeg']; exact hqdeg'.ne'
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_root (q - Polynomial.C 1) hpdeg
  have hprod : ∏ t ∈ T, (w - ι t) = 1 := by
    have h := hw
    rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_C, sub_eq_zero, hq, Polynomial.eval_prod] at h
    simpa only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] using h
  have hw1 : Valued.v w ≤ 1 := by
    by_contra h
    rw [not_le] at h
    have hfac : ∀ t ∈ T, Valued.v (w - ι t) = Valued.v w := fun t ht => by
      rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_left _ (by rw [Valuation.map_neg]; exact (hT t ht).trans_lt h)]
    have h2 : Valued.v (∏ t ∈ T, (w - ι t)) = Valued.v w ^ T.card := by
      rw [map_prod, Finset.prod_congr rfl hfac, Finset.prod_const]
    rw [hprod, Valuation.map_one] at h2
    exact absurd h2 (ne_of_lt (one_lt_pow₀ h hcard.ne'))
  have hfac : ∀ t ∈ T, Valued.v (w - ι t) = 1 := by
    have hle : ∀ t ∈ T, Valued.v (w - ι t) ≤ 1 := fun t ht =>
      (Valuation.map_sub _ _ _).trans (max_le hw1 (hT t ht))
    exact (Finset.prod_eq_one_iff_of_le_one' hle).1 (by rw [← map_prod, hprod, Valuation.map_one])
  refine ⟨w, (mem_affinoid_iff' P 0 w).2 ⟨by rw [pow_zero]; exact hw1, fun a => ?_⟩⟩
  rw [pow_zero]
  rcases le_or_gt (Valued.v (algebraMap K₀ K a)) 1 with ha | ha
  · obtain ⟨t, ht, hat⟩ := hTcov a ha
    have hsplit : w - algebraMap K₀ K a = (w - ι t) + (ι t - algebraMap K₀ K a) := by rw [hι]; ring
    have hlt : Valued.v (ι t - algebraMap K₀ K a) < Valued.v (w - ι t) := by
      rw [hfac t ht, ← Valuation.map_neg, neg_sub]; exact hat
    rw [hsplit, Valuation.map_add_eq_of_lt_left _ hlt, hfac t ht]
  · have hlt : Valued.v w < Valued.v (-(algebraMap K₀ K a)) := by
      rw [Valuation.map_neg]; exact hw1.trans_lt ha
    rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_right _ hlt, Valuation.map_neg]
    exact ha.le

theorem theta_self_eq_one [DecidableEq K] {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) {x y a : K}
    (hx : ∀ γ : G, pmoebius K₀ (ρ γ) x ≠ a) (hy : ∀ γ : G, pmoebius K₀ (ρ γ) y ≠ a) :
    theta ρ x y a a = 1 := by
  unfold theta
  have : thetaFactor ρ x y a a = fun _ => 1 := funext fun γ => by
    unfold thetaFactor
    exact CerednikDrinfeld.Omega.crossRatio_self a _ _ (hx γ).symm (hy γ).symm
  rw [this, tprod_one]

theorem pmoebius_mk_diag [DecidableEq K] (n : GL (Fin 2) K₀) (π : K₀) (hπ : π ≠ 0)
    (hn : (n : Matrix (Fin 2) (Fin 2) K₀) = !![1, 0; 0, π]) (w : K) :
    pmoebius K₀ (Matrix.ProjGenLinGroup.mk n) (algebraMap K₀ K π * w) = w := by
  have h00 : n 0 0 = 1 := by change (n : Matrix (Fin 2) (Fin 2) K₀) 0 0 = 1; rw [hn]; simp
  have h01 : n 0 1 = 0 := by change (n : Matrix (Fin 2) (Fin 2) K₀) 0 1 = 0; rw [hn]; simp
  have h10 : n 1 0 = 0 := by change (n : Matrix (Fin 2) (Fin 2) K₀) 1 0 = 0; rw [hn]; simp
  have h11 : n 1 1 = π := by change (n : Matrix (Fin 2) (Fin 2) K₀) 1 1 = π; rw [hn]; simp
  have hπ' : algebraMap K₀ K π ≠ 0 := (map_ne_zero _).2 hπ
  have hden : algebraMap K₀ K (n 1 0) * (algebraMap K₀ K π * w) + algebraMap K₀ K (n 1 1) ≠ 0 := by
    rw [h10, h11, map_zero, zero_mul, zero_add]; exact hπ'
  rw [pmoebius_mk K₀ n _ hden, moebius, h00, h01, h10, h11, map_one, map_zero, one_mul, add_zero, zero_mul,
    zero_add, mul_div_cancel_left₀ _ hπ']

theorem sum_walkCycle_cons_nil
    {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (τ : W → ZMod 2) (hτ : ∀ (g : G) (w : W), τ (g • w) = τ w) (hadj : ∀ u v : W, 𝒯.Adj u v → τ u ≠ τ v)
    [DecidableEq (QuotEdge G 𝒯)] {E : Type} [Fintype E]
    (eE : E ≃ {e : QuotEdge G 𝒯 // τ e.out.fst = 0}) (e₀ : E) (v₀ : W) (β : G)
    {u v : W} (h : 𝒯.Adj u v) (hd : (⟨(u, v), h⟩ : 𝒯.Dart) = (eE e₀).1.out) :
    (∑ e : E, ((stabWidth G 𝒯 (eE e).1 : ℕ) : ℤ) * pathCycle 𝒯 (fun e' => (eE e').1) v₀ β e *
        walkCycle 𝒯 (fun e' => (eE e').1) (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil : 𝒯.Walk u v) e) =
      ((stabWidth G 𝒯 (eE e₀).1 : ℕ) : ℤ) * pathCycle 𝒯 (fun e' => (eE e').1) v₀ β e₀ := by
  classical
  have key : ∀ e : E, walkCycle 𝒯 (fun e' => (eE e').1) (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil : 𝒯.Walk u v) e
      = if e = e₀ then 1 else 0 := by
    intro e
    rw [walkCycle_cons, walkCycle_nil, Pi.zero_apply, add_zero, hd, dartIndex]
    have h2 : Quotient.mk (orbitRel G 𝒯.Dart) (eE e₀).1.out.symm ≠ (eE e).1 := by
      intro hq
      have hrel : (orbitRel G 𝒯.Dart) (eE e₀).1.out.symm (eE e).1.out :=
        Quotient.exact (hq.trans (Quotient.out_eq (eE e).1).symm)
      obtain ⟨γ, hγ⟩ := MulAction.orbitRel_apply.1 hrel
      have h0 : τ (eE e₀).1.out.symm.fst = 0 := by
        rw [← hγ, smul_dart_fst, hτ]; exact (eE e).2
      have hs : (eE e₀).1.out.symm.fst = (eE e₀).1.out.snd := rfl
      rw [hs] at h0
      exact hadj _ _ (eE e₀).1.out.adj ((eE e₀).2.trans h0.symm)
    rw [if_neg h2, sub_zero, Quotient.out_eq]
    by_cases he : e = e₀
    · subst he; simp
    · have : (eE e₀).1 ≠ (eE e).1 := fun h' => he (eE.injective (Subtype.ext h')).symm
      rw [if_neg this, if_neg he]
  simp_rw [key]
  simp [Finset.sum_ite_eq']

end EdgePairResidue
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_exists_pair_v_theta_eq_one_and_v_theta_mul_zpow_sub_one_lt_forall_ne_pmoebius.UAP"

theorem solution
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ ε)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (ϖ₁ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ₁) [IsDomain ↥(holRing ϖ₁)]
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀))
    [MulAction G (LT.LatticeTree.Vertex R K₀)]
    [CerednikDrinfeld.Mumford.GraphAction G (CerednikDrinfeld.BruhatTits.tree R K₀)]
    (hρ : CerednikDrinfeld.Mumford.ActsThrough (LT.LatticeTree.Vertex R K₀) ρ)

    (hfin : ∀ w : LT.LatticeTree.Vertex R K₀, Finite (MulAction.stabilizer G w))
    [Finite (CerednikDrinfeld.Mumford.QuotVert G (LT.LatticeTree.Vertex R K₀))]
    (τ : LT.LatticeTree.Vertex R K₀ → ZMod 2) (hτ : ∀ (g : G) (w : LT.LatticeTree.Vertex R K₀), τ (g • w) = τ w)
    (hadj : ∀ u w : LT.LatticeTree.Vertex R K₀, (CerednikDrinfeld.BruhatTits.tree R K₀).Adj u w → τ u ≠ τ w)
    (htame : ∀ w : LT.LatticeTree.Vertex R K₀, Valued.v ((Nat.card ↥(MulAction.stabilizer G w) : ℕ) : K) = 1)

    (z₀ : K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)

    [DecidableEq (CerednikDrinfeld.Mumford.QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀))]
    {E : Type} [Fintype E]
    (eE : E ≃ {e : CerednikDrinfeld.Mumford.QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀) // τ e.out.fst = 0})
    (e₀ : E) (ζ : Kˣ) (hζ : Valued.v ((ζ : Kˣ) : K) = 1)

    (S : Finset ↥(upperHalfPlane K₀ K)) :
    ∃ a b : K, a ∈ upperHalfPlane K₀ K ∧ b ∈ upperHalfPlane K₀ K ∧
      (∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) ∧ (∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀) ∧
      (∀ s ∈ S, ∀ (δ : G), a ≠ pmoebius K₀ (ρ δ) (s : K) ∧ b ≠ pmoebius K₀ (ρ δ) (s : K)) ∧
      ∀ β : G, Valued.v (theta ρ a b z₀ (pmoebius K₀ (ρ β) z₀)) = 1 ∧
        Valued.v (theta ρ a b z₀ (pmoebius K₀ (ρ β) z₀) *
            (((ζ : Kˣ) : K) ^ (((CerednikDrinfeld.Mumford.stabWidth G (CerednikDrinfeld.BruhatTits.tree R K₀) (eE e₀).1 : ℕ) : ℤ) *
              CerednikDrinfeld.Mumford.pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e' => (eE e').1)
                (LT.LatticeTree.stdVertex R K₀) β e₀))⁻¹ - 1) < 1 := by
  classical

  let P : PseudoUniformizer K₀ K := UAP.treePseudoUniformizer hϖ hint hv
  have hPϖ : algebraMap K₀ K P.ϖ = algebraMap K₀ K (algebraMap R K₀ ϖ) := rfl
  have hunif : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ Valued.v (algebraMap K₀ K P.ϖ) ∨
      1 ≤ Valued.v (algebraMap K₀ K a) := UAP.v_algebraMap_le_or_one_le hϖ hint hv
  obtain ⟨T, hT, hTcov, hTsep⟩ := UAP.exists_finset_residue_representatives (K := K) hϖ hint hv
  have hexP : IsExhausted P := EdgePairResidue.isExhausted_of_forall_exists_pow_le ϖ₁ P hex hq
  have hdisc : IsDiscrete K ρ := EdgePairResidue.S1_isDiscrete R K₀ ϖ hϖ K hint hv hq ρ hρ hfin
  have hπ0 : (0 : Γ₀) < Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) := P.pos
  have hπ1 : Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) < 1 := P.lt_one
  have hπK : algebraMap K₀ K (algebraMap R K₀ ϖ) ≠ 0 := (Valuation.ne_zero_iff _).1 hπ0.ne'
  have hϖK₀ : algebraMap R K₀ ϖ ≠ 0 := UAP.algebraMap_ne_zero_of_irreducible hϖ

  let nM : GL (Fin 2) K₀ := Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 0, algebraMap R K₀ ϖ]
    (by rw [Matrix.det_fin_two_of]; simpa using hϖK₀)
  have hn : (nM : Matrix (Fin 2) (Fin 2) K₀) = !![1, 0; 0, algebraMap R K₀ ϖ] := rfl
  let sM : R → GL (Fin 2) K₀ := fun t => Matrix.GeneralLinearGroup.mkOfDetNeZero !![algebraMap R K₀ t, 1; 1, 0]
    (by rw [Matrix.det_fin_two_of]; simp)
  have hs : ∀ t : R, (sM t : Matrix (Fin 2) (Fin 2) K₀) = !![algebraMap R K₀ t, 1; 1, 0] := fun t => rfl

  obtain ⟨g, t, hg1, hg2⟩ :=
    CerednikDrinfeld.BruhatTits.exists_smul_stdVertex_eq_fst_and_mul_smul_stdVertex_eq_snd
      R K₀ ϖ hϖ nM hn sM hs (eE e₀).1.out
  have hst : sM t • LT.LatticeTree.stdVertex R K₀ = LT.LatticeTree.stdVertex R K₀ :=
    (CerednikDrinfeld.BruhatTits.adj_stdVertex_iff_eq_smul_of_uniformizer R K₀ ϖ hϖ nM hn sM hs).2.1 t
  obtain ⟨h, hh⟩ : ∃ h : GL (Fin 2) K₀, h = g * sM t := ⟨_, rfl⟩
  have hh1 : h • LT.LatticeTree.stdVertex R K₀ = (eE e₀).1.out.fst := by rw [hh, mul_smul, hst, hg1]
  have hh2 : (h * nM) • LT.LatticeTree.stdVertex R K₀ = (eE e₀).1.out.snd := by rw [hh]; exact hg2
  have hadj₀ : (CerednikDrinfeld.BruhatTits.tree R K₀).Adj (h • LT.LatticeTree.stdVertex R K₀)
      ((h * nM) • LT.LatticeTree.stdVertex R K₀) := by
    rw [hh1, hh2]; exact (eE e₀).1.out.adj
  have hdart : (⟨(h • LT.LatticeTree.stdVertex R K₀, (h * nM) • LT.LatticeTree.stdVertex R K₀), hadj₀⟩ :
      (CerednikDrinfeld.BruhatTits.tree R K₀).Dart) = (eE e₀).1.out :=
    SimpleGraph.Dart.ext _ _ (Prod.ext hh1 hh2)

  obtain ⟨gc, hgc⟩ : ∃ gc : PGL(2, K₀), gc = Matrix.ProjGenLinGroup.mk (h * nM) := ⟨_, rfl⟩

  let Bad : K → Set K := fun y => {x : K | x ∈ affinoid P 1 ∧ ∃ γ : G, pmoebius K₀ (ρ γ) y = pmoebius K₀ gc x}
  have hBadZ : (Bad z₀).Finite := EdgePairResidue.finite_pullback P hexP ρ hdisc gc hz₀
  have hBadS : ∀ s : ↥(upperHalfPlane K₀ K), (Bad (s : K)).Finite :=
    fun s => EdgePairResidue.finite_pullback P hexP ρ hdisc gc s.2
  let F : Set K := Bad z₀ ∪ ⋃ s ∈ (S : Set ↥(upperHalfPlane K₀ K)), Bad (s : K)
  have hF : F.Finite := hBadZ.union (Set.Finite.biUnion S.finite_toSet fun s _ => hBadS s)
  obtain ⟨a', ha', haF, hbF⟩ := BetaGlue.exists_mem_stdEdgeTube_not_mem P hunif ((ζ : Kˣ) : K) hζ F hF
  have hb' : ((ζ : Kˣ) : K) * a' ∈ stdEdgeTube P :=
    EdgePairResidue.mem_stdEdgeTube_of_v_eq P hunif ha' (by rw [Valuation.map_mul, hζ, one_mul])
  have ha'1 : a' ∈ affinoid P 1 := BetaGlue.stdEdgeTube_subset_affinoid_one P hunif ha'
  have hb'1 : ((ζ : Kˣ) : K) * a' ∈ affinoid P 1 := BetaGlue.stdEdgeTube_subset_affinoid_one P hunif hb'
  have ha'0 : a' ≠ 0 := (Valuation.ne_zero_iff _).1 (hπ0.trans ha'.2.1).ne'
  have haZ : ∀ γ : G, pmoebius K₀ (ρ γ) z₀ ≠ pmoebius K₀ gc a' :=
    fun γ hγ => haF (Or.inl ⟨ha'1, γ, hγ⟩)
  have hbZ : ∀ γ : G, pmoebius K₀ (ρ γ) z₀ ≠ pmoebius K₀ gc (((ζ : Kˣ) : K) * a') :=
    fun γ hγ => hbF (Or.inl ⟨hb'1, γ, hγ⟩)
  have haS : ∀ s ∈ S, ∀ γ : G, pmoebius K₀ (ρ γ) (s : K) ≠ pmoebius K₀ gc a' :=
    fun s hsS γ hγ => haF (Or.inr (Set.mem_biUnion (Finset.mem_coe.2 hsS) ⟨ha'1, γ, hγ⟩))
  have hbS : ∀ s ∈ S, ∀ γ : G, pmoebius K₀ (ρ γ) (s : K) ≠ pmoebius K₀ gc (((ζ : Kˣ) : K) * a') :=
    fun s hsS γ hγ => hbF (Or.inr (Set.mem_biUnion (Finset.mem_coe.2 hsS) ⟨hb'1, γ, hγ⟩))

  have haΩ : pmoebius K₀ gc a' ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ ha'.1 gc
  have hbΩ : pmoebius K₀ gc (((ζ : Kˣ) : K) * a') ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ hb'.1 gc
  have haz₀ : ∀ γ : G, pmoebius K₀ (ρ γ) (pmoebius K₀ gc a') ≠ z₀ :=
    EdgePairResidue.forall_pmoebius_ne_of_forall_ne ρ haΩ haZ
  have hbz₀ : ∀ γ : G, pmoebius K₀ (ρ γ) (pmoebius K₀ gc (((ζ : Kˣ) : K) * a')) ≠ z₀ :=
    EdgePairResidue.forall_pmoebius_ne_of_forall_ne ρ hbΩ hbZ
  refine ⟨pmoebius K₀ gc a', pmoebius K₀ gc (((ζ : Kˣ) : K) * a'), haΩ, hbΩ, haz₀, hbz₀,
    fun s hsS δ => ⟨fun he => haS s hsS δ he.symm, fun he => hbS s hsS δ he.symm⟩, fun β => ?_⟩

  obtain ⟨U, hU, -, hUθ, -⟩ :=
    CerednikDrinfeld.Omega.exists_isUnit_coe_eq_thetaMer_apply_smul_eq_period_mul K₀ K ϖ₁ hex ρ hdisc hz₀ haΩ haZ β
  obtain ⟨U', hU', hUU'⟩ := BetaGlue.exists_isUnit_coe_eq ϖ₁ P U hU
  obtain ⟨f, hf⟩ : ∃ f : ↥(holRing P), f = gc⁻¹ • U' := ⟨_, rfl⟩
  have hfU : IsUnit f := by
    rw [hf]; exact hU'.map (MulSemiringAction.toRingHom PGL(2, K₀) ↥(holRing P) gc⁻¹)
  have hfapp : ∀ z : ↥(upperHalfPlane K₀ K),
      (f : ↥(upperHalfPlane K₀ K) → K) z = (U : ↥(upperHalfPlane K₀ K) → K) (gc • z) := by
    intro z; rw [hf, coe_smul_holRing_apply, inv_inv, hUU']

  obtain ⟨c, m, hc0, hres⟩ :=
    CerednikDrinfeld.Omega.exists_v_apply_div_sub_one_lt_of_isUnit_of_mem_stdEdgeTube P hrk hunif f hfU
  have hjump := CerednikDrinfeld.Omega.v_apply_eq_and_v_apply_eq_mul_zpow_of_isUnit_of_forall_mem_stdEdgeTube
    P hrk hunif T hT hTcov hTsep f hfU (Valued.v c) m (fun z hz => (hres z hz).2)
  have hvc0 : Valued.v c ≠ 0 := (Valuation.ne_zero_iff _).2 hc0

  obtain ⟨w₀, hw₀⟩ := EdgePairResidue.exists_mem_affinoid_zero P T hT hTcov
  have hw₀Ω : w₀ ∈ upperHalfPlane K₀ K := affinoid_subset_upperHalfPlane P 0 hw₀
  have hw₀' : w₀ ∈ affinoid ϖ₁ 0 := by
    rw [(CerednikDrinfeld.Omega.holRing_eq_and_affinoid_zero_eq ϖ₁ P).2]; exact hw₀
  have hπw₀Ω : algebraMap K₀ K (algebraMap R K₀ ϖ) * w₀ ∈ upperHalfPlane K₀ K := by
    rw [mem_upperHalfPlane_iff] at hw₀Ω ⊢
    intro x hx
    apply hw₀Ω (x / algebraMap R K₀ ϖ)
    rw [map_div₀, hx, mul_div_cancel_left₀ _ hπK]
  have hnw : Matrix.ProjGenLinGroup.mk nM • (⟨algebraMap K₀ K (algebraMap R K₀ ϖ) * w₀, hπw₀Ω⟩ :
      ↥(upperHalfPlane K₀ K)) = ⟨w₀, hw₀Ω⟩ :=
    Subtype.ext (EdgePairResidue.pmoebius_mk_diag nM (algebraMap R K₀ ϖ) hϖK₀ hn w₀)
  have hi : Valued.v ((U : ↥(upperHalfPlane K₀ K) → K) (gc • ⟨w₀, hw₀Ω⟩)) = Valued.v c := by
    rw [← hfapp]; exact hjump.1 ⟨w₀, hw₀Ω⟩ hw₀
  have hii : Valued.v ((U : ↥(upperHalfPlane K₀ K) → K) (Matrix.ProjGenLinGroup.mk h • ⟨w₀, hw₀Ω⟩)) =
      Valued.v c * Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ m := by
    have h2 := hjump.2 ⟨algebraMap K₀ K (algebraMap R K₀ ϖ) * w₀, hπw₀Ω⟩ (by
      show (algebraMap K₀ K P.ϖ)⁻¹ * (algebraMap K₀ K (algebraMap R K₀ ϖ) * w₀) ∈ affinoid P 0
      rw [hPϖ, inv_mul_cancel_left₀ hπK]; exact hw₀)
    rw [hfapp, hgc, map_mul, mul_smul, hnw] at h2
    rw [h2, hPϖ]

  have hflow :=
    CerednikDrinfeld.Omega.v_apply_smul_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq_of_isUnit_of_eq_theta
      R K₀ ϖ hϖ K hint hv hq hrk ϖ₁ hex ρ hρ hfin τ hτ hadj htame eE hz₀ haΩ haZ β U hU hUθ
      h (h * nM) w₀ w₀ hw₀' hw₀' (SimpleGraph.Walk.cons hadj₀ SimpleGraph.Walk.nil)
  rw [EdgePairResidue.sum_walkCycle_cons_nil (CerednikDrinfeld.BruhatTits.tree R K₀) τ hτ hadj eE e₀
    (LT.LatticeTree.stdVertex R K₀) β hadj₀ hdart, ← hgc, hi, hii] at hflow
  have hmN : (((CerednikDrinfeld.Mumford.stabWidth G (CerednikDrinfeld.BruhatTits.tree R K₀) (eE e₀).1 : ℕ) : ℤ) *
      CerednikDrinfeld.Mumford.pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e' => (eE e').1)
        (LT.LatticeTree.stdVertex R K₀) β e₀) = m :=
    zpow_right_injective₀ hπ0 hπ1.ne (mul_left_cancel₀ hvc0 hflow)

  have hβZ : ∀ γ : G, pmoebius K₀ (ρ γ) (pmoebius K₀ (ρ β) z₀) ≠ pmoebius K₀ gc a' := fun γ => by
    rw [← pmoebius_mul K₀ hz₀, ← map_mul]; exact haZ (γ * β)
  have hUa : (U : ↥(upperHalfPlane K₀ K) → K) (gc • ⟨a', ha'.1⟩) = 1 := by
    rw [hUθ (gc • ⟨a', ha'.1⟩) (not_exists.2 fun γ => haZ γ)]
    exact EdgePairResidue.theta_self_eq_one ρ haZ hβZ
  have hUb : (U : ↥(upperHalfPlane K₀ K) → K) (gc • ⟨((ζ : Kˣ) : K) * a', hb'.1⟩) =
      theta ρ (pmoebius K₀ gc a') (pmoebius K₀ gc (((ζ : Kˣ) : K) * a')) z₀ (pmoebius K₀ (ρ β) z₀) := by
    rw [hUθ (gc • ⟨((ζ : Kˣ) : K) * a', hb'.1⟩) (not_exists.2 fun γ => hbZ γ)]
    have h4 := CerednikDrinfeld.Omega.theta_pmoebius_mul_theta_eq_theta ρ haΩ hbΩ hz₀ haΩ haz₀ hbz₀ haZ β
      (CerednikDrinfeld.Omega.thetaMultipliable_of_isDiscrete_of_isExhausted ϖ₁ hex ρ hdisc haΩ hbΩ hz₀
        (pmoebius_mem_upperHalfPlane K₀ hz₀ (ρ β)))
      (CerednikDrinfeld.Omega.thetaMultipliable_of_isDiscrete_of_isExhausted ϖ₁ hex ρ hdisc hz₀
        (pmoebius_mem_upperHalfPlane K₀ hz₀ (ρ β)) haΩ haΩ)
    rw [EdgePairResidue.theta_self_eq_one ρ haZ hβZ, mul_one] at h4
    exact h4.symm

  obtain ⟨hra1, hra2⟩ := hres a' ha'
  obtain ⟨hrb1, hrb2⟩ := hres (((ζ : Kˣ) : K) * a') hb'
  rw [hfapp, hUa] at hra1 hra2
  rw [hfapp, hUb] at hrb1 hrb2
  refine ⟨?_, ?_⟩
  · rw [hrb2, Valuation.map_mul, hζ, one_mul, ← hra2, Valuation.map_one]
  · rw [hmN]
    exact EdgePairResidue.pu_final hc0 ha'0 (Units.ne_zero ζ) hra1 hrb1

end S_CerednikDrinfeld_Omega_exists_pair_v_theta_eq_one_and_v_theta_mul_zpow_sub_one_lt_forall_ne_pmoebius
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_pair_v_theta_eq_one_and_v_theta_mul_zpow_sub_one_lt_forall_ne_pmoebius (solution)
