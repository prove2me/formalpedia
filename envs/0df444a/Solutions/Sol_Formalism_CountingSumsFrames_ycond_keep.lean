-- Prove2me | solution 1 for Formalism.CountingSumsFrames.ycond_keep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:24:31.74093+00:00
-- url     : https://prove2.me/submissions/f70a5cb5-0089-4aa1-9fd8-6bf66c0663c8

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime]
namespace Formalism.CountingSumsFrames
theorem _root_.solution {N r : ℕ} [NeZero r] (LL : Letters N) (j : ℕ) (Mt : WithTop ℤ)
    (T : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hc : ∀ c d x, T (glAct p LL j c d x) = glAct p LL j c d (T x))
    (hw : ∀ x ∈ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt},
      T x ∈ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt}) :
    ∀ x ∈ YCond p (r := r) LL j Mt, T x ∈ YCond p (r := r) LL j Mt := by
  unfold YCond
  set F := {S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) |
    S ≤ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt} ∧ GlStable p LL j S}
    with hF
  have hle : sSup F ≤ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt} :=
    sSup_le fun S hS => hS.1
  have hst : GlStable p LL j (sSup F) := by
    intro c d
    have : sSup F ≤ (sSup F).comap (glAct p LL j c d) :=
      sSup_le fun S hS x hx => le_sSup hS (hS.2 c d x hx)
    exact fun x hx => this hx
  have hmap : (sSup F).map T ∈ F := by
    refine ⟨Submodule.map_le_iff_le_comap.mpr (fun x hx => hw x (hle hx)), ?_⟩
    intro c d y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    rw [← hc]
    exact Submodule.mem_map_of_mem (hst c d x hx)
  intro x hx
  exact le_sSup hmap (Submodule.mem_map_of_mem hx)
end Formalism.CountingSumsFrames
