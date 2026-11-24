-- Prove2me | solution 1 for Formalism.GM.FrozenVariableComponents.ycond_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:22.002808+00:00
-- url     : https://prove2.me/submissions/2df154e9-eb05-4995-8a29-e9475655818a

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_ycond_stable
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_wt_le_of_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset Formalism.GM.M
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
variable [NeZero r]
namespace Formalism.GM.FrozenVariableComponents
theorem _root_.solution {NA NB : ℕ} (LA : Letters NA) (LB : Letters NB) (jA jB : ℕ) (M : WithTop ℤ)
    (P : MvPolynomial (Fin NA × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin NB × Fin r) ℚ_[p])
    (hc : ∀ c d F, P (glAct p LA jA c d F) = glAct p LB jB c d (P F))
    (hs : ∀ F, ∀ m ∈ (P F).support, ∃ m0 ∈ F.support, wt LB jB 0 m = wt LA jA 0 m0) :
    ∀ F ∈ YCond p LA jA M, P F ∈ YCond p LB jB M := by
  intro F hF
  have hS : Submodule.map P (Formalism.GM.M.YCond p LA jA M) ≤ Formalism.GM.M.YCond p LB jB M := by
    have hmem : Submodule.map P (Formalism.GM.M.YCond p LA jA M) ∈
        {S | S ≤ MvPolynomial.restrictSupport ℚ_[p]
          {m : Fin NB × Fin r →₀ ℕ | ((Formalism.GM.M.wt LB jB 0 m : ℤ) : WithTop ℤ) ≤ M} ∧ Formalism.GM.M.GlStable p LB jB S} := by
      refine ⟨?_, ?_⟩
      · intro y hy
        obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
        rw [mem_restrictSupport_iff]
        intro m hm
        obtain ⟨m0, hm0, hw⟩ := hs x m (Finset.mem_coe.1 hm)
        show ((Formalism.GM.M.wt LB jB 0 m : ℤ) : WithTop ℤ) ≤ M
        rw [hw]
        exact wt_le_of_mem p LA jA M x hx m0 hm0
      · intro c d y hy
        obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
        exact Submodule.mem_map.2 ⟨_, ycond_stable p LA jA M c d x hx, hc c d x⟩
    unfold Formalism.GM.M.YCond
    exact le_sSup hmem
  exact hS (Submodule.mem_map_of_mem hF)
end Formalism.GM.FrozenVariableComponents
