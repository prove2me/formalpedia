-- Prove2me | solution 1 for Formalism.HN.ex_slopes
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:23.480089+00:00
-- url     : https://prove2.me/submissions/6b427636-92c1-4fbb-aa87-cd368b4fb0b2

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNSlopes
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Example

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
open Formalism Formalism.HN
open PolygonExample
local notation "ρx" => AddMonoidHom.id E2
namespace Formalism.HN
theorem _root_.solution (n : ℕ) (s : Fin n → ℝ) (hn : n = 2) (hanti : Antitone s)
    (hpos : ∀ θ : ℝ, 0 < θ → (Finset.univ.filter (fun j => θ ≤ s j)).card = 0)
    (h0 : (Finset.univ.filter (fun j => (0 : ℝ) ≤ s j)).card = 1)
    (hsum : ∑ j, s j = - Real.log 2) :
    ∀ j : Fin n, s j = if (j : ℕ) = 0 then 0 else - Real.log 2 := by
  subst hn
  have hle : ∀ j, s j ≤ 0 := by
    intro j
    by_contra h
    push_neg at h
    have := hpos (s j) h
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at this
    exact this (Finset.mem_univ j) le_rfl
  have h10 : s 1 ≤ s 0 := hanti (by decide)
  have hs1 : s 1 < 0 := by
    by_contra h
    push_neg at h
    have hu : (Finset.univ.filter (fun j : Fin 2 => (0 : ℝ) ≤ s j)) = Finset.univ := by
      ext j
      fin_cases j <;> simp <;> linarith
    rw [hu] at h0
    simp at h0
  have hs0 : s 0 = 0 := by
    by_contra h
    have hlt : s 0 < 0 := lt_of_le_of_ne (hle 0) h
    have he : (Finset.univ.filter (fun j : Fin 2 => (0 : ℝ) ≤ s j)) = ∅ := by
      ext j
      fin_cases j <;> simp <;> linarith
    rw [he] at h0
    simp at h0
  rw [Fin.sum_univ_two, hs0, zero_add] at hsum
  intro j
  fin_cases j <;> simp [hs0, hsum]
end Formalism.HN
