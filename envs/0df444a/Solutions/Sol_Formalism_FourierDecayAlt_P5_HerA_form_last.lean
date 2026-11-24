-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.HerA.form_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:44:03.094919+00:00
-- url     : https://prove2.me/submissions/1c6a5cc2-b2bd-4124-b391-c21c894316ef

import Definitions.Def_Formalism_HermitianCurvature_TopDensNonnegOfKappa
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HsInnerAddSmulRight
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMemMatrixAlgebra
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumPairAtStarMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P5.HerA
theorem _root_.solution (μ : Measure (Mt k r)) (x y : Ix S → RadSp k r z z' π π') (c : Fin r → ℂ) :
    form μ (Fin.last r) x y c = ∑ a, pairAt μ (x a) (y a) c := by
  have : IsEmpty {l : Fin r // (Fin.last r).val ≤ l.val} := ⟨fun l => absurd l.2 (not_le.mpr l.1.isLt)⟩
  have hg : ∀ c' : Cf r (Fin.last r), glue (Fin.last r) c c' = c :=
    fun c' => funext fun l => dif_neg (not_le.mpr l.isLt)
  have hp : ∀ c' : Cf r (Fin.last r), ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) = 1 := fun c' => by
    rw [Fintype.prod_empty, Complex.ofReal_one]
  have h1 : (volume : Measure (Cf r (Fin.last r))) Set.univ = 1 := by
    rw [MeasureTheory.volume_pi, Measure.pi_univ, Fintype.prod_empty]
  unfold form
  simp only [hg, hp, one_mul]
  rw [integral_const]
  simp [measureReal_def, h1]
end Formalism.FourierDecayAlt.P5.HerA
