-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.mem_vars_subG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:18:18.534617+00:00
-- url     : https://prove2.me/submissions/899f3d06-e979-42a8-be10-35ab12fdbcaf

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GramMatrixMulRight
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SelfConjugateRowData
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjCharts
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h3


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj
variable {C : Type} [Field C] {T Orb : Type} [Fintype Orb] {r : T → ℕ} {tau : Orb → ZMod 2 → T}
  {gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C} {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution {Q : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C} {ℓ : Letter T r n}
    (h : ℓ ∈ (subG r tau gm plc Q).vars) : ∃ z, ℓ = lam r tau plc z := by
  unfold subG at h
  rw [MvPolynomial.aeval_eq_bind₁] at h
  obtain ⟨y, _, hy⟩ := MvPolynomial.mem_vars_bind₁ _ _ h
  have h1 := MvPolynomial.vars_sum_subset _ _ hy
  rw [Finset.mem_biUnion] at h1
  obtain ⟨col, _, h2⟩ := h1
  have h3 := MvPolynomial.vars_mul _ _ h2
  rw [MvPolynomial.vars_C, Finset.empty_union, MvPolynomial.vars_X, Finset.mem_singleton] at h3
  exact ⟨((eW r tau N y).1, col), h3⟩
end Formalism.L2.FormalSeriesBounds.RF
