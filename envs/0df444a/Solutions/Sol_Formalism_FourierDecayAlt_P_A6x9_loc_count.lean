-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x9.loc_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:26:31.942693+00:00
-- url     : https://prove2.me/submissions/d79cf5bd-0477-4139-a5b6-0638fd274cfa

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PadicChangeOfVariables
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x9_mem_mulR
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x9_hb1
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x9_hb2
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x9_hb3
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x9_card_map_mk
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_lat_mulR
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_relIndex_ne_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val
attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply



set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x9
variable {K : Type} [CommRing K]
variable [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K} {ψ : AddChar K ℂ}
variable (π : Kˣ)
namespace Formalism.FourierDecayAlt.P.A6x9
theorem _root_.solution (hd : LocalDatum K R ψ) (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K))
    (hπ : (π : K) ∈ R) (hπ' : ∀ x : K, ∃ m : ℕ, (π : K) ^ m * x ∈ R) {m k k' i : ℕ} {si z0 z0i : K}
    (hs : ((m + 1 : ℕ) : K) * si = 1) (hk : (π : K) ^ k * si ∈ R) (hz0 : z0 * z0i = 1)
    (hk' : (π : K) ^ k' * z0i ∈ R) (T : Kˣ) (cr : K ⧸ R.toAddSubgroup → Kˣ) (hcr : IsCr R cr)
    (a : Kˣ) (ha : (a : K) * (T : K) = ((m + 1 : ℕ) : K) * z0 ^ m * (π : K) ^ (k + 1 + k' + i))
    (haR : ((a⁻¹ : Kˣ) : K) ∈ R) :
    {p : (K ⧸ R.toAddSubgroup) × Kˣ | (p.2 : K) - z0 ∈ mulR R ((π : K) ^ (k + 1 + k' + i)) ∧
      p.2 ^ (m + 1) = T * cr p.1}.Finite ∧
    ({p : (K ⧸ R.toAddSubgroup) × Kˣ | (p.2 : K) - z0 ∈ mulR R ((π : K) ^ (k + 1 + k' + i)) ∧
      p.2 ^ (m + 1) = T * cr p.1}.ncard : ℝ) = modK R (a : K) := by
  set S : Set ((K ⧸ R.toAddSubgroup) × Kˣ) :=
    {p | (p.2 : K) - z0 ∈ mulR R ((π : K) ^ (k + 1 + k' + i)) ∧ p.2 ^ (m + 1) = T * cr p.1} with hS
  obtain ⟨c0, hc0⟩ : ∃ c0 : K, c0 = z0 ^ (m + 1) * ((T⁻¹ : Kˣ) : K) := ⟨_, rfl⟩
  have hTi : (T : K) * ((T⁻¹ : Kˣ) : K) = 1 := by simp
  have hai : (a : K) * ((a⁻¹ : Kˣ) : K) = 1 := by simp
  have hle : R.toAddSubgroup ≤ mulR R (a : K) := by
    intro r hr
    exact mem_mulR.2 ⟨((a⁻¹ : Kˣ) : K) * r, R.mul_mem haR hr, by rw [← mul_assoc, hai, one_mul]⟩
  set X : Set (K ⧸ R.toAddSubgroup) := (fun x => ((c0 : K) : K ⧸ R.toAddSubgroup) + x) ''
    ((mulR R (a : K)).map (QuotientAddGroup.mk' R.toAddSubgroup) : Set (K ⧸ R.toAddSubgroup)) with hX
  have hinj : Set.InjOn Prod.fst S := by
    rintro ⟨x, z⟩ ⟨h1, h2⟩ ⟨x', z'⟩ ⟨h1', h2'⟩ hxx
    simp only at hxx h1 h2 h1' h2'
    subst hxx
    have h3 : (z : K) ^ (m + 1) = (z' : K) ^ (m + 1) := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, h2, h2']
    have := hb2 π hd hn hπ hπ' hs hk hz0 hk' h1 h1' h3
    rw [Units.ext this]
  have himg : Prod.fst '' S = X := by
    apply Set.Subset.antisymm
    · rintro _ ⟨⟨x, z⟩, ⟨h1, h2⟩, rfl⟩
      simp only at h1 h2 ⊢
      obtain ⟨b, hb, h3⟩ := hb1 π hπ hs hk hz0 hk' h1
      obtain ⟨r, hr, rfl⟩ := mem_mulR.1 hb
      have h4 : (z : K) ^ (m + 1) = (T : K) * (cr x : K) := by
        rw [← Units.val_pow_eq_pow_val, h2, Units.val_mul]
      have h5 : (cr x : K) = c0 + (a : K) * r := by
        rw [hc0]
        linear_combination ((T⁻¹ : Kˣ) : K) * (h3 - h4 - r * ha) +
          ((a : K) * r - (cr x : K)) * hTi
      refine ⟨(((a : K) * r : K) : K ⧸ R.toAddSubgroup), ⟨(a : K) * r, mem_mulR.2 ⟨r, hr, rfl⟩, rfl⟩, ?_⟩
      show ((c0 : K) : K ⧸ R.toAddSubgroup) + (((a : K) * r : K) : K ⧸ R.toAddSubgroup) = x
      rw [← QuotientAddGroup.mk_add, ← h5]
      exact hcr x
    · rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
      obtain ⟨r, hr, rfl⟩ := mem_mulR.1 hl
      set x : K ⧸ R.toAddSubgroup := ((c0 : K) : K ⧸ R.toAddSubgroup) +
        (QuotientAddGroup.mk' R.toAddSubgroup) ((a : K) * r) with hx
      have h1 : ((cr x : K) : K ⧸ R.toAddSubgroup) = ((c0 + (a : K) * r : K) : K ⧸ R.toAddSubgroup) := by
        rw [hcr x, hx]; rfl
      have h2 : -(c0 + (a : K) * r) + (cr x : K) ∈ R.toAddSubgroup := (QuotientAddGroup.eq).1 h1.symm
      obtain ⟨r', hr', hr2⟩ : ∃ r' ∈ R, r' = -(c0 + (a : K) * r) + (cr x : K) := ⟨_, h2, rfl⟩
      obtain ⟨ρ, hρ⟩ : ∃ ρ : K, ρ = r + ((a⁻¹ : Kˣ) : K) * r' := ⟨_, rfl⟩
      have hρR : ρ ∈ R := by rw [hρ]; exact R.add_mem hr (R.mul_mem haR hr')
      obtain ⟨z, hz, hz2⟩ := hb3 π hd hn hπ hπ' hs hk hz0 hk'
        (mem_mulR.2 ⟨ρ, hρR, rfl⟩ : (π : K) ^ (k + 1 + k' + i) * ρ ∈ _)
      have h3 : z ^ (m + 1) = (T : K) * (cr x : K) := by
        rw [hz2, hρ]
        have e1 : (cr x : K) = c0 + (a : K) * r + r' := by rw [hr2]; ring
        rw [e1, hc0]
        linear_combination (-(r + ((a⁻¹ : Kˣ) : K) * r')) * ha + (T : K) * r' * hai -
          z0 ^ (m + 1) * hTi
      have hzu : IsUnit z := by
        have : IsUnit (z ^ (m + 1)) := by rw [h3]; exact (T * cr x).isUnit
        exact (isUnit_pow_iff (by omega)).1 this
      obtain ⟨zu, rfl⟩ := hzu
      refine ⟨(x, zu), ⟨hz, ?_⟩, rfl⟩
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, h3, Units.val_mul]
  have hcard : X.ncard = R.toAddSubgroup.relIndex (mulR R (a : K)) := by
    rw [hX, Set.ncard_image_of_injective _ (add_right_injective _), ← card_map_mk]
    exact (Nat.card_coe_set_eq _).symm
  have hne : R.toAddSubgroup.relIndex (mulR R (a : K)) ≠ 0 :=
    A5x5.relIndex_ne_zero hd.isOpen (A5x5.lat_mulR hd.isOpen hd.isCompact a).cp
  have hXfin : X.Finite := Set.finite_of_ncard_ne_zero (by rw [hcard]; exact hne)
  refine ⟨Set.Finite.of_finite_image (by rw [himg]; exact hXfin) hinj, ?_⟩
  rw [← hinj.ncard_image, himg, hcard]
  unfold modK
  rw [AddSubgroup.relIndex_eq_one.2 hle]
  simp
end Formalism.FourierDecayAlt.P.A6x9
