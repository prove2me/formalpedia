-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.Herm4.ortho_fam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:03:18.089441+00:00
-- url     : https://prove2.me/submissions/10cc1bad-560c-4477-a118-95838966e033

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PFourSq
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_FS_Herm4_ortho_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Module
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
variable {K : Type} [Field K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (c : K →+* K) (h : V → V → K)
variable {c h}
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
namespace Herm4
theorem _root_.solution (H : Herm4 c h) (m : ℕ) (hm : m ≤ finrank K V) :
    ∃ v : Fin m → V, (∀ i, v i ≠ 0) ∧ ∀ i j, i ≠ j → h (v i) (v j) = 0 := by
  induction m with
  | zero => exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ m ih =>
    obtain ⟨v, hv0, hv⟩ := ih (by omega)
    let L : V →ₗ[K] (Fin m → K) := LinearMap.pi (fun i => H.hl (v i))
    have hrank := LinearMap.finrank_range_add_finrank_ker L
    have hr : finrank K (LinearMap.range L) ≤ m := by
      calc finrank K (LinearMap.range L) ≤ finrank K (Fin m → K) := Submodule.finrank_le _
        _ = m := by simp
    have hker : LinearMap.ker L ≠ ⊥ := by
      intro hb
      rw [hb, finrank_bot] at hrank
      omega
    obtain ⟨x, hxk, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    have hx : ∀ i, h x (v i) = 0 := fun i => by
      have h1 := congrFun (LinearMap.mem_ker.mp hxk) i
      simpa [L, Herm4.hl] using h1
    refine ⟨Fin.snoc (α := fun _ => V) v x, fun i => ?_, fun i j hij => ?_⟩
    · induction i using Fin.lastCases with
      | last => simpa using hx0
      | cast i => simpa using hv0 i
    · induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd rfl hij
        | cast j => simpa using hx j
      | cast i =>
        induction j using Fin.lastCases with
        | last => simpa using H.ortho_symm (hx i)
        | cast j =>
          simp only [Fin.snoc_castSucc]
          exact hv i j (fun e => hij (by rw [e]))
end Herm4
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
