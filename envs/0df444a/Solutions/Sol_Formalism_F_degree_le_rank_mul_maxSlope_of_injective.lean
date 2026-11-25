-- Prove2me | solution 1 for Formalism.F.degree_le_rank_mul_maxSlope_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:13:47.28645+00:00
-- url     : https://prove2.me/submissions/f67bc946-c99c-41ea-8bd9-94286673e960

import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_LatticeSlopes_CovolAntiSameRank
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqGram
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolPos
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DegQuot
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_GramDetLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_SlopesBdd
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_SlopeLeMuMaxOf
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_SlopeInequality
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_OrthSum
import Theorems.Thm_Formalism_F_covol_basic_properties
import Theorems.Thm_Formalism_F_gram_det_le
import Theorems.Thm_Formalism_F_slopeInequality_of
import Theorems.Thm_Formalism_F_slopeLeMuMax_of
import Theorems.Thm_Formalism_F_slopesBdd_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.F
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
namespace Formalism.F
theorem _root_.solution (Q M : Submodule ℤ E) (hQ : DiscreteTopology Q)
    (hM : DiscreteTopology M) (ψ : Q →ₗ[ℤ] M) (hinj : Function.Injective ψ)
    (hψ : ∀ x : Q, ‖((ψ x : M) : E)‖ ≤ ‖(x : E)‖) : deg Q ≤ rk Q * muMax M := by
  haveI := hQ
  by_cases hQ0 : Q = ⊥
  · subst hQ0
    have h0 : covol (⊥ : Submodule ℤ E) = 1 := (covol_basic_properties E).1
    have hr : rk (⊥ : Submodule ℤ E) = 0 := by simp [rk]
    simp [deg, h0, hr]
  · have hs := slopeInequality_of (slopeLeMuMax_of (slopesBdd_of gram_det_le)) E E Q M hQ hM hQ0
      ψ 1 hinj (fun x => by simpa using hψ x)
    rw [Real.log_one, add_zero] at hs
    have hk : 0 < rk Q := Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hQ0)
    have hk' : (0 : ℝ) < (rk Q : ℝ) := by exact_mod_cast hk
    unfold slope at hs
    rw [div_le_iff₀ hk'] at hs
    linarith
end Formalism.F
