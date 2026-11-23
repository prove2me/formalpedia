-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact.haar_closed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:53:54.70483+00:00
-- url     : https://prove2.me/submissions/4cfe5f79-2e92-4475-b755-5e7820607927

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GLRealOpen
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GlR
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsClosedLowUni
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_GeneralLinearIntegersOpenCompact_haar_of_cover
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_GeneralLinearIntegersOpenCompact_conj_entry
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_GeneralLinearIntegersOpenCompact_exists_pow_int
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_GeneralLinearIntegersOpenCompact_glR_open
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_GeneralLinearIntegersOpenCompact_glR_compact
import Theorems.Thm_UpperTheory_Reformulated_B_GLRealOpen_glR_open


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Measure Topology Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
namespace Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact
theorem _root_.solution [T2Space K] (R : Subring K) (hRo : IsOpen (R : Set K))
    (hRc : IsCompact (R : Set K)) (ϖ : Kˣ) (hϖ : (ϖ : K) ∈ R)
    (hx : ∀ x : K, ∃ m : ℕ, (ϖ : K) ^ m * x ∈ R) {n : ℕ}
    (H : Subgroup (GL (Fin n) K)) (hH : IsClosed (H : Set (GL (Fin n) K))) (e : Fin n → ℕ)
    (hstr : ∀ g ∈ H, ∀ a b, (g : Matrix (Fin n) (Fin n) K) a b = 0 ∨
      (a = b ∧ (g : Matrix (Fin n) (Fin n) K) a b = 1) ∨ e a < e b) :
    ∃ μ : Measure H, μ.IsMulLeftInvariant ∧ μ.IsMulRightInvariant ∧ SFinite μ ∧
      μ (intSub R H : Set H) = 1 := by
  let δ : ℕ → Fin n → Kˣ := fun m a => ϖ ^ (m * e a)
  let f : ℕ → GL (Fin n) K → GL (Fin n) K := fun m g => (Dg (δ m))⁻¹ * g * Dg (δ m)
  have hf : ∀ m, Continuous (f m) := fun m =>
    (continuous_const.mul continuous_id).mul continuous_const
  let M : ℕ → Subgroup (GL (Fin n) K) := fun m =>
    (glR R n).comap (MulAut.conj (Dg (δ m))⁻¹).toMonoidHom
  have hMset : ∀ m, (M m : Set (GL (Fin n) K)) = f m ⁻¹' (glR R n : Set _) := by
    intro m; ext g
    show (MulAut.conj (Dg (δ m))⁻¹) g ∈ glR R n ↔ (Dg (δ m))⁻¹ * g * Dg (δ m) ∈ glR R n
    rw [MulAut.conj_apply, inv_inv]
  let L : ℕ → Subgroup H := fun m => (M m).comap H.subtype
  have hemb : IsClosedEmbedding (H.subtype) := hH.isClosedEmbedding_subtypeVal
  have hK : (intSub R H : Set H) = H.subtype ⁻¹' (glR R n : Set _) := by ext g; rfl
  have hL : ∀ m, (L m : Set H) = H.subtype ⁻¹' (M m : Set _) := fun m => rfl
  refine haar_of_cover (intSub R H) ?_ ?_ L ?_ ?_ ?_
  · rw [hK]; exact (glR_open R hRo n).preimage continuous_subtype_val
  · rw [hK]; exact hemb.isCompact_preimage (glR_compact R hRc n)
  · intro m; rw [hL, hMset]
    exact ((glR_open R hRo n).preimage (hf m)).preimage continuous_subtype_val
  · intro m; rw [hL, hMset]
    have hc : IsCompact (f m ⁻¹' (glR R n : Set _)) := by
      let h : GL (Fin n) K ≃ₜ GL (Fin n) K :=
        (Homeomorph.mulLeft (Dg (δ m))⁻¹).trans (Homeomorph.mulRight (Dg (δ m)))
      exact h.isCompact_preimage.2 (glR_compact R hRc n)
    exact hemb.isCompact_preimage hc
  · intro g
    obtain ⟨m1, hm1⟩ := exists_pow_int R ϖ hϖ hx e _ (hstr g g.2)
    obtain ⟨m2, hm2⟩ := exists_pow_int R ϖ hϖ hx e _ (hstr (g : GL (Fin n) K)⁻¹ (H.inv_mem g.2))
    refine ⟨max m1 m2, ?_⟩
    have hmem : (g : GL (Fin n) K) ∈ (M (max m1 m2) : Set _) := by
      rw [hMset]
      refine ⟨fun a b => ?_, fun a b => ?_⟩
      · show (((Dg (δ (max m1 m2)))⁻¹ * (g : GL (Fin n) K) * Dg (δ (max m1 m2)) : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) a b ∈ R
        rw [conj_entry]; exact hm1 _ (le_max_left _ _) a b
      · have hinv : (f (max m1 m2) g)⁻¹ =
            (Dg (δ (max m1 m2)))⁻¹ * (g : GL (Fin n) K)⁻¹ * Dg (δ (max m1 m2)) := by
          simp [f, mul_assoc]
        show (((f (max m1 m2) g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b ∈ R
        rw [hinv, conj_entry]; exact hm2 _ (le_max_right _ _) a b
    exact hmem
end Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact
