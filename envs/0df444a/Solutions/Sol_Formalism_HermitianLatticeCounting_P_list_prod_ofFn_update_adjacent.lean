-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.list_prod_ofFn_update_adjacent
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:34.943691+00:00
-- url     : https://prove2.me/submissions/20e14748-9f27-4049-8b5d-d62a9ea3236d

import Definitions.Def_Formalism_FlagUnipotentLattices_QDetNegTranspose
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LanglandsParameterEquivariant
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_AntisymmetrizedProductEqFactorialSmulQdet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S8 Formalism.REAL TensorProduct Finset
set_option linter.all false
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {A : Type} [Ring A] {t : ℕ} (f g : Fin t → A) (i : ℕ) (hi : i + 1 < t)
    (h : ∀ k : Fin t, (k : ℕ) ≠ i → (k : ℕ) ≠ i + 1 → g k = f k) :
    (List.ofFn g).prod = ((List.ofFn f).take i).prod * (g ⟨i, by omega⟩ * g ⟨i + 1, hi⟩) *
      ((List.ofFn f).drop (i + 2)).prod := by
  have hg : ∀ k : Fin t, (k : ℕ) ≠ i → (k : ℕ) ≠ i + 1 → g k = f k := h
  have htake : (List.ofFn g).take i = (List.ofFn f).take i := by
    apply List.ext_getElem
    · simp
    · intro j h1 h2
      simp only [List.getElem_take, List.getElem_ofFn]
      simp only [List.length_take, List.length_ofFn] at h1
      exact hg _ (by simp; omega) (by simp; omega)
  have hdrop : (List.ofFn g).drop (i + 2) = (List.ofFn f).drop (i + 2) := by
    apply List.ext_getElem
    · simp
    · intro j h1 h2
      simp only [List.getElem_drop, List.getElem_ofFn]
      exact hg _ (by simp; omega) (by simp; omega)
  rw [← List.take_append_drop i (List.ofFn g), List.drop_eq_getElem_cons (by simp; omega),
    List.drop_eq_getElem_cons (by simp; omega), htake, List.getElem_ofFn, List.getElem_ofFn,
    show i + 1 + 1 = i + 2 from rfl, hdrop]
  simp only [List.prod_append, List.prod_cons, mul_assoc]
end Formalism.HermitianLatticeCounting.P
