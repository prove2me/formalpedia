-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.coefficient_bound_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:33:57.722262+00:00
-- url     : https://prove2.me/submissions/4ed668d6-f98c-45f5-8566-f2a3c5f131dd

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_CoefficientBoundHolds
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_CoefficientBoundLemmas_key

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas
open Formalism.NormUnitaryCountingLemmas.CoefficientBoundLemmas
namespace Formalism.NormUnitaryCountingLemmas
theorem _root_.solution : CB := by
  intro R _ _ _ ϖ hϖ S _ _ _ N n hlen I Φ e hΦ ρ φ J
  classical
  let ψ : (Fin ρ → R) →ₗ[R] S := Fintype.linearCombination R φ
  let P : Submodule R (Fin ρ → R) := N.comap ψ
  have hP : Module.length R ((Fin ρ → R) ⧸ P) ≤ n := by
    refine le_trans (Module.length_le_of_injective (P.mapQ N ψ le_rfl) ?_) hlen
    rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ]
    simp [P]
  obtain ⟨G, hG, c, hc⟩ := key P n hP ϖ hϖ
  let A : Matrix (Fin ρ) (Fin ρ) (FractionRing R) := Matrix.of fun a b => Φ (φ a) (J b)
  have hentry : ∀ i b, ∃ r : R, algebraMap R (FractionRing R) ϖ ^ e *
      ((G.map (algebraMap R (FractionRing R))) * A) i b = algebraMap R (FractionRing R) r := by
    intro i b
    have : ((G.map (algebraMap R (FractionRing R))) * A) i b = Φ (ψ (G i)) (J b) := by
      simp [Matrix.mul_apply, A, ψ, Fintype.linearCombination_apply, map_sum, map_smul,
        Algebra.smul_def]
    rw [this]
    exact hΦ _ (hG i) (J b)
  choose r hr using hentry
  have hϖK : algebraMap R (FractionRing R) ϖ ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective R (FractionRing R))]
    exact hϖ.ne_zero
  have hdet : algebraMap R (FractionRing R) ϖ ^ ((ρ : ℤ) * e) *
      ((G.map (algebraMap R (FractionRing R))) * A).det =
        algebraMap R (FractionRing R) (Matrix.of r).det := by
    rw [RingHom.map_det]
    have : (algebraMap R (FractionRing R)).mapMatrix (Matrix.of r) =
        (algebraMap R (FractionRing R) ϖ ^ e) • ((G.map (algebraMap R (FractionRing R))) * A) := by
      ext i b
      simp [← hr i b]
    rw [this, Matrix.det_smul, Fintype.card_fin, ← zpow_natCast, ← zpow_mul, mul_comm e]
  refine ⟨c * (Matrix.of r).det, ?_⟩
  rw [zpow_add₀ hϖK, zpow_natCast, ← map_pow, hc, map_mul, map_mul, ← hdet, Matrix.det_mul,
    RingHom.map_det]
  simp only [RingHom.mapMatrix_apply]
  ring
end Formalism.NormUnitaryCountingLemmas
