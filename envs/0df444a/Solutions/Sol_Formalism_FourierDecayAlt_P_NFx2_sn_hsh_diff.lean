-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sn_hsh_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:21:08.386658+00:00
-- url     : https://prove2.me/submissions/67e3dd69-a784-4680-911f-70dc8bd24cd3

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFx2
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF
noncomputable section
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {L : R.LevelData A P.r}
  {κ : (M.Ty P → ℂ) →ₐ[ℂ] A} {SS : ℕ → A}
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution {l j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) (hlj : l ≠ j) (ρ : M.Ty P) (Y : ℂ) :
    sn_hsh P l j ρ Y = (Y + M.rho P ρ j + 1) * M.xEx P {l, j} ρ Y := by
  unfold M.xEx sn_hsh
  have hjm : j ∈ Icc 1 (P.k - 1) \ {l} := Finset.mem_sdiff.2 ⟨hj, by simpa using hlj.symm⟩
  rw [Finset.prod_eq_mul_prod_sdiff_singleton j _ (fun h => absurd hjm h)]
  congr 1
  · simp; ring
  · have e : (Icc 1 (P.k - 1) \ {l}) \ {j} = Icc 1 (P.k - 1) \ {l, j} := by
      ext i; simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_insert]; tauto
    rw [e]
    refine Finset.prod_congr rfl fun i hi => ?_
    have : i ≠ j := fun e' => (Finset.mem_sdiff.1 hi).2 (by simp [e'])
    simp [this]
end Formalism.FourierDecayAlt.P.NFx2
