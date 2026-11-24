-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.H_poly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:19:24.747799+00:00
-- url     : https://prove2.me/submissions/146cab78-d262-42cc-b7ca-e262d1852377

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
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {L0 : PreLevel A P.r}
  {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution (h : SHyp P L0 QQ κ) (a b : Fin 2) : IsPF fun Y => QQ Y a b := by
  obtain ⟨n, C, hC, -⟩ := h.2.2.2.2.2.2.2.2.1
  refine ⟨∑ j ∈ Finset.range n, Polynomial.monomial j (C a b j), fun Y => ?_⟩
  show QQ Y a b = _
  rw [hC, ev, Polynomial.eval₂_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval₂_monomial, RingHom.id_apply, ← map_pow, ← Algebra.commutes, Algebra.smul_def]
end Formalism.FourierDecayAlt.P.NFx2
