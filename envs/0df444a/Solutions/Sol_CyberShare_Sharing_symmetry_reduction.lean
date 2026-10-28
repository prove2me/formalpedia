-- Prove2me | solution 1 for CyberShare.Sharing.symmetry_reduction
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T05:53:22.731453+00:00
-- url     : https://prove2.me/submissions/01f145e9-d413-48fe-b58f-94e32a581674

import Mathlib
import Definitions.Def_CyberShare_Sharing_Model

open CyberShare.Sharing

namespace CyberShare.Sharing.SymAux

def sw (w : Outcome) : Outcome := ⟨w.st, w.y2, w.y1, w.attack2, w.attack1⟩

lemma sw_sw (w : Outcome) : sw (sw w) = w := by cases w; rfl

lemma prob_sw (P : Params) (w : Outcome) : prob P (sw w) = prob P w := by
  unfold prob sw; simp only []; ring

lemma payoff2_sw (P : Params) (A B : Sig → Sig → ℝ) (w : Outcome) :
    payoff2 P A B (sw w) = payoff1 P B A w := rfl

lemma payoff1_sw (P : Params) (A B : Sig → Sig → ℝ) (w : Outcome) :
    payoff1 P A B (sw w) = payoff2 P B A w := rfl

lemma sum_cell (P : Params) (o : Dec) (y y' : Sig) (f : Outcome → ℝ) :
    ∑ w ∈ cell2 o y y', f w = ∑ w ∈ cell1 o y y', f (sw w) := by
  apply Finset.sum_nbij' sw sw
  · intro w hw; simp only [cell1, cell2, sw, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    tauto
  · intro w hw; simp only [cell1, cell2, sw, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    tauto
  · intro w _; exact sw_sw w
  · intro w _; exact sw_sw w
  · intro w _; rfl

lemma key (P : Params) (o : Dec) (A B : Sig → Sig → ℝ) (y y' : Sig) :
    ∑ w ∈ cell2 o y y', prob P w * payoff2 P A B w =
      ∑ w ∈ cell1 o y y', prob P w * payoff1 P B A w := by
  rw [sum_cell P o y y']
  apply Finset.sum_congr rfl
  intro w _
  rw [prob_sw, payoff2_sw]

lemma key' (P : Params) (o : Dec) (A B : Sig → Sig → ℝ) (y y' : Sig) :
    ∑ w ∈ cell1 o y y', prob P w * payoff1 P A B w =
      ∑ w ∈ cell2 o y y', prob P w * payoff2 P B A w := (key P o B A y y').symm

lemma inv_swap (P : Params) (s1 s2 : Dec) (K1 K2 : Sig → Sig → ℝ) :
    IsInvEq P s1 s2 K1 K2 → IsInvEq P s2 s1 K2 K1 := by
  rintro ⟨h1, h2, h3, h4, h5⟩
  refine ⟨h2, h1, fun y y' => ⟨(h3 y y').2, (h3 y y').1⟩, ?_, ?_⟩
  · intro y y' x hx
    have := h5 y y' x hx
    rw [key] at this
    rw [key] at this
    exact this
  · intro y y' x hx
    have := h4 y y' x hx
    rw [key'] at this
    rw [key'] at this
    exact this

lemma exAnte_swap (P : Params) (K1 K2 : Sig → Sig → ℝ) :
    exAnte2 P K1 K2 = exAnte1 P K2 K1 := by
  unfold exAnte1 exAnte2
  rw [← Equiv.sum_comp (⟨sw, sw, sw_sw, sw_sw⟩ : Outcome ≃ Outcome)]
  apply Finset.sum_congr rfl
  intro w _
  simp only [Equiv.coe_fn_mk]
  rw [prob_sw, payoff2_sw]

end CyberShare.Sharing.SymAux

open CyberShare.Sharing.SymAux in
theorem solution (P : Params) (hP : P.Standing) :
    (∀ s1 s2 K1 K2, IsInvEq P s1 s2 K1 K2 ↔ IsInvEq P s2 s1 K2 K1) ∧
    (∀ K1 K2, exAnte2 P K1 K2 = exAnte1 P K2 K1) ∧
    ((∃ K1 K2, IsInvEq P .S .S K1 K2) →
     (∃ K1 K2, IsInvEq P .N .S K1 K2) →
     (IsSharingEq P .S .S ↔
       ∀ K1 K2 K1' K2', IsInvEq P .S .S K1 K2 → IsInvEq P .N .S K1' K2' →
         exAnte1 P K1' K2' ≤ exAnte1 P K1 K2)) := by
  have h1 : ∀ s1 s2 K1 K2, IsInvEq P s1 s2 K1 K2 ↔ IsInvEq P s2 s1 K2 K1 :=
    fun s1 s2 K1 K2 => ⟨inv_swap P s1 s2 K1 K2, inv_swap P s2 s1 K2 K1⟩
  refine ⟨h1, exAnte_swap P, ?_⟩
  intro hSS hNS
  obtain ⟨K1, K2, hNS⟩ := hNS
  constructor
  · rintro ⟨_, _, _, hA, _⟩
    intro K1 K2 K1' K2' hSS' hNS'
    exact hA K1 K2 K1' K2' hSS' hNS'
  · intro H
    refine ⟨hSS, ⟨K1, K2, hNS⟩, ?_, H, ?_⟩
    · exact ⟨K2, K1, (h1 _ _ _ _).1 hNS⟩
    · intro K1 K2 K1' K2' hSS' hSN'
      rw [exAnte_swap, exAnte_swap]
      exact H K2 K1 K2' K1' ((h1 _ _ _ _).1 hSS') ((h1 _ _ _ _).1 hSN')
