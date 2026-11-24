-- Prove2me | solution 1 for FFactor.exists_factor_of_matching
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:54:19.574005+00:00
-- url     : https://prove2.me/submissions/0a2c998d-f212-46f6-8422-c0f9eed54de0

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorGadget
public import Theorems.Thm_FFactor_gadget_adj_inl_inl
public import Theorems.Thm_FFactor_gadget_adj_inl_inr
public import Theorems.Thm_FFactor_gadget_adj_inr_inl
public import Theorems.Thm_FFactor_gadget_adj_inr_inr
attribute [local simp] FFactor.gadget_adj_inl_inl
attribute [local simp] FFactor.gadget_adj_inl_inr
attribute [local simp] FFactor.gadget_adj_inr_inl
attribute [local simp] FFactor.gadget_adj_inr_inr

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Classical
open FFactor
variable {V : Type*} [Fintype V] (G : SimpleGraph V) (f : V → ℕ)
variable {G f}
namespace FFactor
theorem _root_.solution (hf : ∀ v, f v ≤ G.degree v) (M : (gadget G f).Subgraph)
    (hM : M.IsPerfectMatching) :
    ∃ H : SimpleGraph V, H ≤ G ∧ ∀ v, #{u | H.Adj v u} = f v := by
  rw [Subgraph.isPerfectMatching_iff] at hM
  obtain ⟨H, hH⟩ : ∃ H : SimpleGraph V, ∀ u w, H.Adj u w ↔
      ∃ h : G.Adj u w, M.Adj (.inl ⟨(u, w), h⟩) (.inl ⟨(w, u), h.symm⟩) :=
    ⟨{ Adj := fun u w => ∃ h : G.Adj u w, M.Adj (.inl ⟨(u, w), h⟩) (.inl ⟨(w, u), h.symm⟩)
       symm := ⟨fun u w ⟨h, h'⟩ => ⟨h.symm, h'.symm⟩⟩
       loopless := ⟨fun u ⟨h, _⟩ => G.loopless.irrefl u h⟩ }, fun _ _ => Iff.rfl⟩
  refine ⟨H, fun u w h => ((hH u w).mp h).1, fun v => ?_⟩
  have huniq : ∀ x y z, M.Adj x y → M.Adj x z → y = z := fun x y z h1 h2 =>
    (hM x).unique h1 h2
  set D : Finset G.Dart := {d | d.fst = v}
  have hD : #D = G.degree v := G.dart_fst_fiber_card_eq_degree v
  have hsplit := card_filter_add_card_filter_not
    (s := D) (fun d => M.Adj (.inl d) (.inl d.symm))
  -- darts matched to their reverse correspond to the `H`-neighbours of `v`
  have h1 : #{d ∈ D | M.Adj (.inl d) (.inl d.symm)} = #{u | H.Adj v u} := by
    apply card_bij (fun d _ => d.snd)
    · rintro ⟨⟨a, b⟩, hab⟩ hd
      simp only [D, mem_filter, mem_univ, true_and] at hd ⊢
      obtain ⟨rfl, hd2⟩ := hd
      exact (hH _ _).mpr ⟨hab, hd2⟩
    · intro d1 hd1 d2 hd2 h
      simp only [D, mem_filter, mem_univ, true_and] at hd1 hd2
      exact Dart.ext _ _ (Prod.ext (hd1.1.trans hd2.1.symm) h)
    · intro u hu
      simp only [mem_filter, mem_univ, true_and] at hu
      obtain ⟨h, hM'⟩ := (hH _ _).mp hu
      exact ⟨⟨(v, u), h⟩, mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, rfl⟩, hM'⟩, rfl⟩
  -- the other darts correspond to the inner vertices of `v`
  have hex : ∀ i : Fin (G.degree v - f v), ∃ d : G.Dart, M.Adj (.inr ⟨v, i⟩) (.inl d) := by
    intro i
    obtain ⟨y, hy, -⟩ := hM (.inr ⟨v, i⟩)
    rcases y with d | q
    · exact ⟨d, hy⟩
    · exact absurd (M.adj_sub hy) (gadget_adj_inr_inr G f)
  have h2 : #(univ : Finset (Fin (G.degree v - f v))) =
      #{d ∈ D | ¬ M.Adj (.inl d) (.inl d.symm)} := by
    apply card_bij (fun i _ => Classical.choose (hex i))
    · intro i _
      have hi := Classical.choose_spec (hex i)
      have hfst : (Classical.choose (hex i)).fst = v := M.adj_sub hi
      simp only [D, mem_filter, mem_univ, true_and]
      refine ⟨hfst, fun h => ?_⟩
      have := huniq _ _ _ hi.symm h
      cases this
    · intro i _ j _ hij
      have hi := Classical.choose_spec (hex i)
      have hj := Classical.choose_spec (hex j)
      rw [hij] at hi
      have := huniq _ _ _ hi.symm hj.symm
      simp only [Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at this
      exact this
    · intro d hd
      simp only [D, mem_filter, mem_univ, true_and] at hd
      obtain ⟨y, hy, -⟩ := hM (.inl d)
      rcases y with d' | ⟨w, i⟩
      · have : d' = d.symm := M.adj_sub hy
        subst this
        exact absurd hy hd.2
      · have hw : d.fst = w := M.adj_sub hy
        have hvw : v = w := hd.1.symm.trans hw
        subst hvw
        refine ⟨i, mem_univ _, ?_⟩
        have hi := Classical.choose_spec (hex i)
        have := huniq _ _ _ hi hy.symm
        simpa using this
  rw [card_univ, Fintype.card_fin] at h2
  have := hf v
  have hs : #{d ∈ D | M.Adj (.inl d) (.inl d.symm)} + #{d ∈ D | ¬ M.Adj (.inl d) (.inl d.symm)} =
      #D := hsplit
  rw [h1, ← h2, hD] at hs
  omega
end FFactor
