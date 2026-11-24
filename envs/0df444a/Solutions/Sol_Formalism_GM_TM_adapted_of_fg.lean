-- Prove2me | solution 1 for Formalism.GM.TM.adapted_of_fg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:39:12.999012+00:00
-- url     : https://prove2.me/submissions/15e8556a-7246-4364-a32e-c275da7bf875

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Theorems.Thm_Formalism_GM_TM_filL_zero
import Theorems.Thm_Formalism_GM_TM_adStep_top
import Theorems.Thm_Formalism_GM_TM_adStep_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.TM
open M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {σ : Type}
namespace Formalism.GM.TM
theorem _root_.solution (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) (v : σ) (hFG : L.FG) (D : ℕ)
    (hD : ∀ x ∈ L, ∀ m ∈ x.support, m v ≤ D) :
    ∃ (n₀ : ℕ) (f : Fin n₀ → MvPolynomial σ ℚ_[p]) (ord : Fin n₀ → ℕ),
      LinearIndependent ℤ_[p] f ∧ Submodule.span ℤ_[p] (Set.range f) = L ∧
      (∀ b, HasOrder v (ord b) (f b)) ∧ ∀ e, Submodule.span ℤ_[p] (f '' {b | e ≤ ord b}) = filL L v e := by
  have hind : ∀ k e, e + k = D + 1 → AdStep L v e := by
    intro k
    induction k with
    | zero => intro e he; rw [show e = D + 1 by omega]; exact adStep_top L v D hD
    | succ k ih => intro e he; exact adStep_succ L v hFG e (ih (e + 1) (by omega))
  obtain ⟨ι, _, f, ord, hli, hsp, hord, hfil⟩ := hind (D + 1) 0 (by omega)
  let eq := Fintype.equivFin ι
  refine ⟨Fintype.card ι, f ∘ eq.symm, ord ∘ eq.symm, hli.comp _ eq.symm.injective, ?_, fun b => (hord _).1, ?_⟩
  · rw [eq.symm.surjective.range_comp, hsp, filL_zero]
  · intro e
    have : (f ∘ eq.symm) '' {b | e ≤ (ord ∘ eq.symm) b} = f '' {i | e ≤ ord i} := by
      ext x
      constructor
      · rintro ⟨b, hb, rfl⟩; exact ⟨eq.symm b, hb, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        refine ⟨eq i, ?_, ?_⟩
        · simp only [Set.mem_setOf_eq, Function.comp_apply, Equiv.symm_apply_apply]; exact hi
        · simp only [Function.comp_apply, Equiv.symm_apply_apply]
    rw [this]
    exact hfil e (Nat.zero_le e)
end Formalism.GM.TM
