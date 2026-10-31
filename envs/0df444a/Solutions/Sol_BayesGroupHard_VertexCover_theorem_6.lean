-- Prove2me | solution 1 for BayesGroupHard.VertexCover.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T23:47:21.209065+00:00
-- url     : https://prove2.me/submissions/b69b2d02-2c84-4acb-8ea1-2d28c312bcd2

import Mathlib
import Definitions.Def_BayesGroupHard_VertexCover_Model
import Theorems.Thm_BayesGroupHard_VertexCover_eq_16

set_option linter.unusedSectionVars false

open Finset

namespace BayesGroupHard.VertexCover

section General
variable {Ag : Type} [Fintype Ag] [DecidableEq Ag]

lemma bvc_sig_add (N : BinNet Ag) (i : Ag) (θ : Bool) :
    sig N i θ false + sig N i θ true = 1 := by
  simp [sig]

lemma bvc_wt_rect (N : BinNet Ag) (θ : Bool) (D : Finset Ag) (g : Ag → Bool) :
    ∑ s ∈ univ.filter (fun s : Ag → Bool => ∀ k ∈ D, s k = g k), jointProb N θ s =
      ∏ k ∈ D, sig N k θ (g k) := by
  have hset : univ.filter (fun s : Ag → Bool => ∀ k ∈ D, s k = g k) =
      Fintype.piFinset (fun k => if k ∈ D then ({g k} : Finset Bool) else univ) := by
    ext s
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h k
      by_cases hk : k ∈ D
      · simp [hk, h k hk]
      · simp [hk]
    · intro h k hk
      have := h k
      simpa [hk] using this
  rw [hset]
  unfold jointProb
  rw [← Finset.prod_univ_sum]
  have : ∀ k, (∑ b ∈ (if k ∈ D then ({g k} : Finset Bool) else univ), sig N k θ b) =
      if k ∈ D then sig N k θ (g k) else 1 := by
    intro k
    by_cases hk : k ∈ D
    · simp [hk]
    · simp only [hk, if_false]
      rw [Fintype.sum_bool, add_comm, bvc_sig_add]
  simp_rw [this]
  rw [Finset.prod_ite_mem, univ_inter]

lemma bvc_post_eq (N : BinNet Ag) (θ : Bool) (I : Finset (Ag → Bool)) :
    post N θ I = (∑ s ∈ I, jointProb N θ s) /
      ((∑ s ∈ I, jointProb N true s) + ∑ s ∈ I, jointProb N false s) := by
  unfold post
  rw [Fintype.sum_bool, ← mul_add, mul_div_mul_left _ _ (by norm_num : (1 / 2 : ℝ) ≠ 0)]

lemma bvc_mapAct_eq (N : BinNet Ag) (I : Finset (Ag → Bool))
    (h0 : 0 ≤ ∑ s ∈ I, jointProb N false s) (h1 : 0 ≤ ∑ s ∈ I, jointProb N true s) :
    mapAct N I = decide ((∑ s ∈ I, jointProb N false s) < ∑ s ∈ I, jointProb N true s) := by
  unfold mapAct
  rw [bvc_post_eq, bvc_post_eq]
  congr 1
  apply propext
  rcases (add_nonneg h1 h0).lt_or_eq with hD | hD
  · exact div_lt_div_iff_of_pos_right hD
  · rw [← hD]
    have e1 : ∑ s ∈ I, jointProb N true s = 0 := by linarith
    have e0 : ∑ s ∈ I, jointProb N false s = 0 := by linarith
    simp [e1, e0]

lemma bvc_actUpTo_eq (N : BinNet Ag) : ∀ t τ, τ < t → ∀ j s, actUpTo N t τ j s = act N τ j s := by
  intro t
  induction t with
  | zero => intro τ h; omega
  | succ t ih =>
    intro τ hτ j s
    show (if τ < t then actUpTo N t τ j s
      else if τ = t then mapAct N (infoUsing N t (actUpTo N t) j s) else false) = _
    by_cases h : τ < t
    · rw [if_pos h, ih τ h]
    · have : τ = t := by omega
      subst this
      rw [if_neg h, if_pos rfl]
      rfl

lemma bvc_infoSet_eq (N : BinNet Ag) (t : ℕ) (i : Ag) (s : Ag → Bool) :
    infoSet N t i s = univ.filter (fun s' => s' i = s i ∧
      ∀ j ∈ N.nbr i, ∀ τ < t, act N τ j s' = act N τ j s) := by
  unfold infoSet infoUsing
  apply Finset.filter_congr
  intro s' _
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun j hj τ hτ => ?_⟩
    rw [← bvc_actUpTo_eq N t τ hτ, ← bvc_actUpTo_eq N t τ hτ]
    exact h2 j hj τ hτ
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun j hj τ hτ => ?_⟩
    rw [bvc_actUpTo_eq N t τ hτ, bvc_actUpTo_eq N t τ hτ]
    exact h2 j hj τ hτ

lemma bvc_infoSet_zero (N : BinNet Ag) (i : Ag) (s : Ag → Bool) :
    infoSet N 0 i s = univ.filter (fun s' : Ag → Bool => ∀ k ∈ ({i} : Finset Ag), s' k = s k) := by
  rw [bvc_infoSet_eq]
  apply Finset.filter_congr
  intro s' _
  simp

lemma bvc_wt_info0 (N : BinNet Ag) (θ : Bool) (i : Ag) (s : Ag → Bool) :
    ∑ s' ∈ infoSet N 0 i s, jointProb N θ s' = sig N i θ (s i) := by
  rw [bvc_infoSet_zero, bvc_wt_rect, prod_singleton]

lemma bvc_act0 (N : BinNet Ag) (i : Ag) (s : Ag → Bool)
    (h : ∀ θ b, 0 ≤ sig N i θ b) :
    act N 0 i s = decide (sig N i false (s i) < sig N i true (s i)) := by
  unfold act
  rw [bvc_mapAct_eq _ _ (by rw [bvc_wt_info0]; exact h _ _) (by rw [bvc_wt_info0]; exact h _ _),
    bvc_wt_info0, bvc_wt_info0]

end General

section VC
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k₀ k₁ : ℝ)

open Agent

lemma bvc_act0_vtx (v : Fin n) (s : Agent n G → Bool) :
    act (vcNet G k₀ k₁) 0 (vtx v) s = s (vtx v) := by
  rw [bvc_act0 _ _ _ (by intro θ b; cases θ <;> cases b <;> norm_num [sig, vcNet])]
  cases s (vtx v) <;> norm_num [sig, vcNet]

lemma bvc_act0_edg (e : G.edgeSet) (s : Agent n G → Bool) :
    act (vcNet G k₀ k₁) 0 (edg e) s = false := by
  rw [bvc_act0 _ _ _ (by intro θ b; cases θ <;> cases b <;> norm_num [sig, vcNet])]
  cases s (edg e) <;> norm_num [sig, vcNet]

lemma bvc_act0_iAg (s : Agent n G → Bool) :
    act (vcNet G k₀ k₁) 0 iAg s = false := by
  rw [bvc_act0 _ _ _ (by intro θ b; cases θ <;> cases b <;> norm_num [sig, vcNet])]
  cases s iAg <;> norm_num [sig, vcNet]

lemma bvc_act0_kap (hk₀ : 0 < k₀) (hk₀' : k₀ < 1) (hk₁ : 0 < k₁) (hk₁' : k₁ < 1)
    (hκ : k₁ < k₀) (s : Agent n G → Bool) :
    act (vcNet G k₀ k₁) 0 kap s = s kap := by
  rw [bvc_act0 _ _ _ (by intro θ b; cases θ <;> cases b <;> simp [sig, vcNet] <;> linarith)]
  cases s kap <;> simp [sig, vcNet] <;> linarith

lemma bvc_info1_edg (e : G.edgeSet) (s : Agent n G → Bool) :
    infoSet (vcNet G k₀ k₁) 1 (edg e) s =
      univ.filter (fun s' => ∀ k ∈ (vcNet G k₀ k₁).nbr (edg e), s' k = s k) := by
  rw [bvc_infoSet_eq]
  apply Finset.filter_congr
  intro s' _
  have hn : (vcNet G k₀ k₁).nbr (edg e) = insert (edg e)
      ((univ.filter (fun v : Fin n => v ∈ (e : Sym2 (Fin n)))).image Agent.vtx) := rfl
  rw [hn]
  simp only [Finset.forall_mem_insert, Finset.forall_mem_image, mem_filter, mem_univ, true_and,
    Nat.lt_one_iff, forall_eq, bvc_act0_vtx, bvc_act0_edg]

lemma bvc_act1_edg (e : G.edgeSet) (x : Agent n G → Bool) :
    act (vcNet G k₀ k₁) 1 (edg e) x = true ↔ ∃ v ∈ (e : Sym2 (Fin n)), x (vtx v) = true := by
  have hw : ∀ θ, ∑ s' ∈ infoSet (vcNet G k₀ k₁) 1 (edg e) x, jointProb (vcNet G k₀ k₁) θ s' =
      ∏ k ∈ (vcNet G k₀ k₁).nbr (edg e), sig (vcNet G k₀ k₁) k θ (x k) := by
    intro θ
    rw [bvc_info1_edg, bvc_wt_rect]
  have hn : (vcNet G k₀ k₁).nbr (edg e) = insert (edg e)
      ((univ.filter (fun v : Fin n => v ∈ (e : Sym2 (Fin n)))).image Agent.vtx) := rfl
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | h u w =>
    have huw : u ≠ w := by
      rw [SimpleGraph.mem_edgeSet] at he
      exact he.ne
    have hfil : univ.filter (fun v : Fin n => v ∈ s(u, w)) = {u, w} := by
      ext v; simp [Sym2.mem_iff]
    have hw' : ∀ θ, ∑ s' ∈ infoSet (vcNet G k₀ k₁) 1 (edg ⟨s(u, w), he⟩) x,
        jointProb (vcNet G k₀ k₁) θ s' =
        sig (vcNet G k₀ k₁) (edg ⟨s(u, w), he⟩) θ (x (edg ⟨s(u, w), he⟩)) *
          (sig (vcNet G k₀ k₁) (vtx u) θ (x (vtx u)) * sig (vcNet G k₀ k₁) (vtx w) θ (x (vtx w))) := by
      intro θ
      rw [hw, hn]
      simp only [Subtype.coe_mk] at *
      rw [hfil, prod_insert (by simp), prod_image (by intro a _ b _ h; simpa using h),
        prod_pair huw]
    unfold act
    generalize hb0 : x (edg ⟨s(u, w), he⟩) = b0 at hw'
    generalize hbu : x (vtx u) = bu at hw'
    generalize hbw : x (vtx w) = bw at hw'
    rw [bvc_mapAct_eq _ _ (by rw [hw']; cases b0 <;> cases bu <;>
        cases bw <;> norm_num [sig, vcNet])
      (by rw [hw']; cases b0 <;> cases bu <;> cases bw <;> norm_num [sig, vcNet]), hw', hw']
    simp only [Subtype.coe_mk, Sym2.mem_iff, exists_eq_or_imp, exists_eq_left, hbu, hbw]
    cases b0 <;> cases bu <;> cases bw <;> norm_num [sig, vcNet]

lemma bvc_fact_2 (s : Agent n G → Bool) :
    G.IsVertexCover {v | s (Agent.vtx v) = true} ↔
      ∀ e : G.edgeSet, act (vcNet G k₀ k₁) 1 (Agent.edg e) s = true := by
  simp only [bvc_act1_edg]
  constructor
  · rintro hC ⟨e, he⟩
    induction e using Sym2.ind with
    | h u w =>
      rw [SimpleGraph.mem_edgeSet] at he
      rcases hC he with h | h
      · exact ⟨u, by simp, h⟩
      · exact ⟨w, by simp, h⟩
  · intro h u w huw
    obtain ⟨v, hv, hsv⟩ := h ⟨s(u, w), huw⟩
    simp only [Sym2.mem_iff] at hv
    rcases hv with rfl | rfl
    · exact Or.inl hsv
    · exact Or.inr hsv

section Time2
variable (hk₀ : 0 < k₀) (hk₀' : k₀ < 1) (hk₁ : 0 < k₁) (hk₁' : k₁ < 1) (hκ : k₁ < k₀)
include hk₀ hk₀' hk₁ hk₁' hκ

lemma bvc_act1_kap (x : Agent n G → Bool) :
    act (vcNet G k₀ k₁) 1 kap x = x kap := by
  have hI : infoSet (vcNet G k₀ k₁) 1 kap x = infoSet (vcNet G k₀ k₁) 0 kap x := by
    rw [bvc_infoSet_eq, bvc_infoSet_eq]
    apply Finset.filter_congr
    intro s' _
    have hn : (vcNet G k₀ k₁).nbr kap = {kap} := rfl
    simp only [hn, Finset.mem_singleton, forall_eq, Nat.lt_one_iff,
      bvc_act0_kap G k₀ k₁ hk₀ hk₀' hk₁ hk₁' hκ, Nat.not_lt_zero]
    constructor
    · rintro ⟨h, _⟩; exact ⟨h, fun _ h' => h'.elim⟩
    · rintro ⟨h, _⟩; exact ⟨h, h⟩
  have h0 := bvc_act0_kap G k₀ k₁ hk₀ hk₀' hk₁ hk₁' hκ x
  unfold act at h0 ⊢
  rw [hI, h0]

lemma bvc_act1_iAg (x : Agent n G → Bool) :
    act (vcNet G k₀ k₁) 1 iAg x = x kap := by
  have hI : infoSet (vcNet G k₀ k₁) 1 iAg x =
      univ.filter (fun s' => ∀ k ∈ ({iAg, kap} : Finset (Agent n G)), s' k = x k) := by
    rw [bvc_infoSet_eq]
    apply Finset.filter_congr
    intro s' _
    have hn : (vcNet G k₀ k₁).nbr iAg = insert iAg (insert kap (univ.image Agent.edg)) := rfl
    simp only [hn, Finset.forall_mem_insert, Finset.forall_mem_image, mem_univ, true_and,
      Nat.lt_one_iff, forall_eq, bvc_act0_kap G k₀ k₁ hk₀ hk₀' hk₁ hk₁' hκ, bvc_act0_iAg,
      bvc_act0_edg, implies_true, and_true, Finset.mem_singleton, forall_eq]
  have hw : ∀ θ, ∑ s' ∈ infoSet (vcNet G k₀ k₁) 1 iAg x, jointProb (vcNet G k₀ k₁) θ s' =
      sig (vcNet G k₀ k₁) iAg θ (x iAg) * sig (vcNet G k₀ k₁) kap θ (x kap) := by
    intro θ
    rw [hI, bvc_wt_rect, prod_pair (by simp)]
  unfold act
  generalize hb0 : x iAg = b0 at hw
  generalize hb1 : x kap = b1 at hw ⊢
  rw [bvc_mapAct_eq _ _ (by rw [hw]; cases b0 <;> cases b1 <;> simp [sig, vcNet] <;> nlinarith)
    (by rw [hw]; cases b0 <;> cases b1 <;> simp [sig, vcNet] <;> nlinarith), hw, hw]
  cases b0 <;> cases b1 <;> simp [sig, vcNet] <;> linarith

lemma bvc_info2 (s : Agent n G → Bool)
    (hedg : ∀ e : G.edgeSet, act (vcNet G k₀ k₁) 1 (Agent.edg e) s = true)
    (hkap : act (vcNet G k₀ k₁) 0 Agent.kap s = false) :
    infoSet (vcNet G k₀ k₁) 2 iAg s =
      univ.filter (fun s' : Agent n G → Bool => s' iAg = s iAg ∧ s' kap = false ∧
        ∀ e : G.edgeSet, act (vcNet G k₀ k₁) 1 (Agent.edg e) s' = true) := by
  rw [bvc_infoSet_eq]
  apply Finset.filter_congr
  intro s' _
  have hn : (vcNet G k₀ k₁).nbr iAg = insert iAg (insert kap (univ.image Agent.edg)) := rfl
  have h2 : ∀ (P : ℕ → Prop), (∀ τ < 2, P τ) ↔ P 0 ∧ P 1 := by
    intro P; constructor
    · intro h; exact ⟨h 0 (by norm_num), h 1 (by norm_num)⟩
    · rintro ⟨h0, h1⟩ τ hτ
      interval_cases τ <;> assumption
  rw [bvc_act0_kap G k₀ k₁ hk₀ hk₀' hk₁ hk₁' hκ] at hkap
  simp only [hn, Finset.forall_mem_insert, Finset.forall_mem_image, mem_univ, true_and, h2,
    bvc_act0_kap G k₀ k₁ hk₀ hk₀' hk₁ hk₁' hκ, bvc_act0_iAg, bvc_act0_edg,
    bvc_act1_kap G k₀ k₁ hk₀ hk₀' hk₁ hk₁' hκ, bvc_act1_iAg G k₀ k₁ hk₀ hk₀' hk₁ hk₁' hκ,
    hedg, hkap, forall_const]
  tauto

end Time2

lemma bvc_fil_iff (C : Finset (Fin n)) (x : Agent n G → Bool) :
    univ.filter (fun v : Fin n => x (vtx v) = true) = C ↔ ∀ v, x (vtx v) = decide (v ∈ C) := by
  rw [Finset.ext_iff]
  apply forall_congr'
  intro v
  simp only [mem_filter, mem_univ, true_and]
  cases h : x (vtx v) <;> by_cases hv : v ∈ C <;> simp [hv]

/-- The profile pinned on agents `i`, `κ` and the vertex agents. -/
def bvcG (C : Finset (Fin n)) (b : Bool) : Agent n G → Bool
  | .vtx v => decide (v ∈ C)
  | .iAg => b
  | _ => false

lemma bvc_prod_vtx (θ : Bool) (C : Finset (Fin n)) :
    ∏ v : Fin n, sig (vcNet G k₀ k₁) (vtx v) θ (decide (v ∈ C)) =
      (if θ then (4 / 10 : ℝ) else 3 / 10) ^ C.card *
        (if θ then (6 / 10 : ℝ) else 7 / 10) ^ (n - C.card) := by
  have h : ∀ v : Fin n, sig (vcNet G k₀ k₁) (vtx v) θ (decide (v ∈ C)) =
      if v ∈ C then (if θ then (4 / 10 : ℝ) else 3 / 10) else (if θ then (6 / 10 : ℝ) else 7 / 10) := by
    intro v
    by_cases hv : v ∈ C <;> cases θ <;> simp [hv, sig, vcNet] <;> norm_num
  simp_rw [h]
  rw [Finset.prod_ite, prod_const, prod_const]
  have h1 : (univ.filter (fun v : Fin n => v ∈ C)).card = C.card := by
    rw [Finset.filter_mem_eq_inter, univ_inter]
  have h2 := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    (fun v => v ∈ C)
  rw [card_univ, Fintype.card_fin] at h2
  rw [h1] at h2 ⊢
  congr 2
  omega

section Time2b
variable (hk₀ : 0 < k₀) (hk₀' : k₀ < 1) (hk₁ : 0 < k₁) (hk₁' : k₁ < 1) (hκ : k₁ < k₀)
include hk₀ hk₀' hk₁ hk₁' hκ

open scoped Classical in
lemma bvc_wt2 (θ : Bool) (s : Agent n G → Bool)
    (hedg : ∀ e : G.edgeSet, act (vcNet G k₀ k₁) 1 (Agent.edg e) s = true)
    (hkap : act (vcNet G k₀ k₁) 0 Agent.kap s = false) :
    ∑ s' ∈ infoSet (vcNet G k₀ k₁) 2 iAg s, jointProb (vcNet G k₀ k₁) θ s' =
      (1 / 2 * (if θ then k₁ else k₀)) *
        ∑ C ∈ univ.filter (fun C : Finset (Fin n) => G.IsVertexCover (C : Set (Fin n))),
          (if θ then (4 / 10 : ℝ) else 3 / 10) ^ C.card *
            (if θ then (6 / 10 : ℝ) else 7 / 10) ^ (n - C.card) := by
  rw [bvc_info2 G k₀ k₁ hk₀ hk₀' hk₁ hk₁' hκ s hedg hkap]
  simp_rw [← bvc_fact_2 G k₀ k₁]
  rw [← Finset.sum_fiberwise_of_maps_to
    (t := univ.filter (fun C : Finset (Fin n) => G.IsVertexCover (C : Set (Fin n))))
    (g := fun s' : Agent n G → Bool => univ.filter (fun v : Fin n => s' (vtx v) = true))]
  swap
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    have : ((univ.filter (fun v : Fin n => x (vtx v) = true) : Finset (Fin n)) : Set (Fin n)) =
        {v | x (vtx v) = true} := by ext v; simp
    rw [this]; exact hx.2.2
  rw [mul_sum]
  apply sum_congr rfl
  intro C hC
  simp only [mem_filter, mem_univ, true_and] at hC
  have hset : (univ.filter (fun s' : Agent n G → Bool => s' iAg = s iAg ∧ s' kap = false ∧
        G.IsVertexCover {v | s' (vtx v) = true})).filter
        (fun s' => univ.filter (fun v : Fin n => s' (vtx v) = true) = C) =
      univ.filter (fun s' : Agent n G → Bool =>
        ∀ k ∈ insert iAg (insert kap (univ.image (Agent.vtx (G := G)))), s' k = bvcG G C (s iAg) k) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, Finset.forall_mem_insert, Finset.forall_mem_image,
      bvc_fil_iff, bvcG, true_implies]
    constructor
    · rintro ⟨⟨h1, h2, _⟩, h4⟩
      exact ⟨h1, h2, h4⟩
    · rintro ⟨h1, h2, h4⟩
      refine ⟨⟨h1, h2, ?_⟩, h4⟩
      have : {v | x (vtx v) = true} = (C : Set (Fin n)) := by
        ext v; simp [h4 v]
      rw [this]; exact hC
  rw [hset, bvc_wt_rect, prod_insert (by simp), prod_insert (by simp),
    prod_image (by intro a _ b _ h; simpa using h)]
  simp only [bvcG]
  rw [bvc_prod_vtx]
  have hi : sig (vcNet G k₀ k₁) iAg θ (s iAg) = 1 / 2 := by
    cases s iAg <;> simp [sig, vcNet] <;> norm_num
  have hk : sig (vcNet G k₀ k₁) kap θ false = if θ then k₁ else k₀ := by
    cases θ <;> simp [sig, vcNet]
  rw [hi, hk]
  ring

end Time2b

end VC

end BayesGroupHard.VertexCover


set_option linter.unusedSectionVars false

open Finset

namespace BayesGroupHard.VertexCover

open Agent

noncomputable def bvcL1 : ℝ := Real.log (4 / 10) - Real.log (3 / 10)
noncomputable def bvcL2 : ℝ := Real.log (6 / 10) - Real.log (7 / 10)

lemma bvc_L1_pos : 0 < bvcL1 := by
  unfold bvcL1
  have := Real.log_lt_log (by norm_num : (0 : ℝ) < 3 / 10) (by norm_num : (3 / 10 : ℝ) < 4 / 10)
  linarith

lemma bvc_L2_neg : bvcL2 < 0 := by
  unfold bvcL2
  have := Real.log_lt_log (by norm_num : (0 : ℝ) < 6 / 10) (by norm_num : (6 / 10 : ℝ) < 7 / 10)
  linarith

lemma bvc_L12_pos : 0 < bvcL1 + bvcL2 := by
  unfold bvcL1 bvcL2
  have h1 := Real.log_lt_log (by norm_num : (0 : ℝ) < 21 / 100) (by norm_num : (21 / 100 : ℝ) < 24 / 100)
  rw [show (21 / 100 : ℝ) = 3 / 10 * (7 / 10) by norm_num, show (24 / 100 : ℝ) = 4 / 10 * (6 / 10) by norm_num,
    Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)] at h1
  linarith

lemma bvc_qtil (α : ℝ) : qtil α = α * bvcL1 + (1 - α) * bvcL2 := by
  unfold qtil qbar qund bvcL1 bvcL2
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_rpow (by norm_num),
    Real.log_rpow (by norm_num), Real.log_rpow (by norm_num), Real.log_rpow (by norm_num)]
  ring

lemma bvc_term (n k : ℕ) (hk : k ≤ n) :
    (4 / 10 : ℝ) ^ k * (6 / 10 : ℝ) ^ (n - k) =
      (3 / 10 : ℝ) ^ k * (7 / 10 : ℝ) ^ (n - k) *
        Real.exp ((k : ℝ) * bvcL1 + ((n : ℝ) - k) * bvcL2) := by
  have hc : (n : ℝ) - k = ((n - k : ℕ) : ℝ) := by push_cast [Nat.cast_sub hk]; ring
  rw [hc, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul]
  have e1 : Real.exp bvcL1 = 4 / 3 := by
    unfold bvcL1; rw [← Real.log_div (by norm_num) (by norm_num), Real.exp_log (by norm_num)]; norm_num
  have e2 : Real.exp bvcL2 = 6 / 7 := by
    unfold bvcL2; rw [← Real.log_div (by norm_num) (by norm_num), Real.exp_log (by norm_num)]; norm_num
  rw [e1, e2, show (4 / 10 : ℝ) = 3 / 10 * (4 / 3) by norm_num,
    show (6 / 10 : ℝ) = 7 / 10 * (6 / 7) by norm_num, mul_pow, mul_pow]
  ring

/-- exponent comparison -/
lemma bvc_exp_cmp (n k : ℕ) (α : ℝ) :
    (k : ℝ) * bvcL1 + ((n : ℝ) - k) * bvcL2 - (n : ℝ) * (α * bvcL1 + (1 - α) * bvcL2) =
      ((k : ℝ) - α * n) * (bvcL1 - bvcL2) := by ring

lemma bvc_a_big (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n) (hk' : (k : ℝ) ≤ 85 / 100 * n) :
    (42 / 100 : ℝ) ^ n < (4 / 10 : ℝ) ^ k * (6 / 10 : ℝ) ^ (n - k) := by
  have hy : (4 / 10 : ℝ) ^ k * (6 / 10 : ℝ) ^ (n - k) = (6 / 10 : ℝ) ^ n * (2 / 3 : ℝ) ^ k := by
    rw [show (4 / 10 : ℝ) = 6 / 10 * (2 / 3) by norm_num, mul_pow]
    rw [show (6 / 10 : ℝ) ^ n = (6 / 10 : ℝ) ^ k * (6 / 10 : ℝ) ^ (n - k) by
      rw [← pow_add, Nat.add_sub_cancel' hk]]
    ring
  rw [hy]
  have h20 : 20 * k ≤ 17 * n := by
    have : (20 * k : ℝ) ≤ 17 * n := by linarith
    exact_mod_cast this
  apply lt_of_pow_lt_pow_left₀ 20 (by positivity)
  rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
  have h1 : (2 / 3 : ℝ) ^ (17 * n) ≤ (2 / 3 : ℝ) ^ (k * 20) := by
    apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
    omega
  have h2 : (42 / 100 : ℝ) ^ (n * 20) < (6 / 10 : ℝ) ^ (n * 20) * (2 / 3 : ℝ) ^ (17 * n) := by
    rw [mul_comm n 20, pow_mul, pow_mul, pow_mul, ← mul_pow]
    apply pow_lt_pow_left₀ (by norm_num) (by positivity) (by omega)
  calc (42 / 100 : ℝ) ^ (n * 20) < (6 / 10 : ℝ) ^ (n * 20) * (2 / 3 : ℝ) ^ (17 * n) := h2
    _ ≤ (6 / 10 : ℝ) ^ (n * 20) * (2 / 3 : ℝ) ^ (k * 20) := by gcongr

open scoped Classical in
noncomputable def bvcA (n : ℕ) (G : SimpleGraph (Fin n)) (a b : ℝ) : ℝ :=
  ∑ C ∈ univ.filter (fun C : Finset (Fin n) => G.IsVertexCover (C : Set (Fin n))),
    a ^ C.card * b ^ (n - C.card)

lemma bvcA_pos (n : ℕ) (G : SimpleGraph (Fin n)) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    0 < bvcA n G a b := by
  classical
  unfold bvcA
  apply Finset.sum_pos' (fun C _ => by positivity)
  refine ⟨univ, ?_, by positivity⟩
  simp

section Post
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k₀ k₁ : ℝ)
variable (hk₀ : 0 < k₀) (hk₀' : k₀ < 1) (hk₁ : 0 < k₁) (hk₁' : k₁ < 1) (hκ : k₁ < k₀)
include hk₀ hk₀' hk₁ hk₁' hκ

lemma bvc_post2 (s : Agent n G → Bool)
    (hedg : ∀ e : G.edgeSet, act (vcNet G k₀ k₁) 1 (Agent.edg e) s = true)
    (hkap : act (vcNet G k₀ k₁) 0 Agent.kap s = false) :
    post (vcNet G k₀ k₁) true (infoSet (vcNet G k₀ k₁) 2 iAg s) =
        k₁ * bvcA n G (4 / 10) (6 / 10) /
          (k₁ * bvcA n G (4 / 10) (6 / 10) + k₀ * bvcA n G (3 / 10) (7 / 10)) ∧
      post (vcNet G k₀ k₁) false (infoSet (vcNet G k₀ k₁) 2 iAg s) =
        k₀ * bvcA n G (3 / 10) (7 / 10) /
          (k₁ * bvcA n G (4 / 10) (6 / 10) + k₀ * bvcA n G (3 / 10) (7 / 10)) := by
  have ht := bvc_wt2 G k₀ k₁ hk₀ hk₀' hk₁ hk₁' hκ true s hedg hkap
  have hf := bvc_wt2 G k₀ k₁ hk₀ hk₀' hk₁ hk₁' hκ false s hedg hkap
  simp only [if_true, Bool.false_eq_true, if_false] at ht hf
  rw [bvc_post_eq, bvc_post_eq, ht, hf]
  unfold bvcA
  have key : ∀ X Y Z : ℝ, (1 / 2 * Z) / (1 / 2 * (k₁ * X + k₀ * Y)) =
      Z / (k₁ * X + k₀ * Y) := by
    intro X Y Z
    rw [mul_div_mul_left _ _ (by norm_num)]
  constructor
  · rw [← key]; congr 1 <;> ring
  · rw [← key]; congr 1 <;> ring

end Post

lemma bvc_term_le (n k : ℕ) (hk : k ≤ n) (α : ℝ) (h : (k : ℝ) ≤ α * n) :
    (4 / 10 : ℝ) ^ k * (6 / 10 : ℝ) ^ (n - k) ≤
      Real.exp ((n : ℝ) * qtil α) * ((3 / 10 : ℝ) ^ k * (7 / 10 : ℝ) ^ (n - k)) := by
  rw [bvc_term n k hk, bvc_qtil, mul_comm (Real.exp _)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.2
  have h1 := bvc_exp_cmp n k α
  have h2 : ((k : ℝ) - α * n) * (bvcL1 - bvcL2) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith [bvc_L1_pos, bvc_L2_neg])
  linarith

lemma bvc_term_ge (n k : ℕ) (hk : k ≤ n) (α : ℝ) (h : α * n ≤ (k : ℝ)) :
    Real.exp ((n : ℝ) * qtil α) * ((3 / 10 : ℝ) ^ k * (7 / 10 : ℝ) ^ (n - k)) ≤
      (4 / 10 : ℝ) ^ k * (6 / 10 : ℝ) ^ (n - k) := by
  rw [bvc_term n k hk, bvc_qtil, mul_comm (Real.exp _)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.2
  have h1 := bvc_exp_cmp n k α
  have h2 : 0 ≤ ((k : ℝ) - α * n) * (bvcL1 - bvcL2) :=
    mul_nonneg (by linarith) (by linarith [bvc_L1_pos, bvc_L2_neg])
  linarith

lemma bvc_term_gt (n k : ℕ) (hk : k ≤ n) (α : ℝ) (h : α * n < (k : ℝ)) :
    Real.exp ((n : ℝ) * qtil α) * ((3 / 10 : ℝ) ^ k * (7 / 10 : ℝ) ^ (n - k)) <
      (4 / 10 : ℝ) ^ k * (6 / 10 : ℝ) ^ (n - k) := by
  rw [bvc_term n k hk, bvc_qtil, mul_comm (Real.exp _)]
  apply mul_lt_mul_of_pos_left _ (by positivity)
  apply Real.exp_lt_exp.2
  have h1 := bvc_exp_cmp n k α
  have h2 : 0 < ((k : ℝ) - α * n) * (bvcL1 - bvcL2) :=
    mul_pos (by linarith) (by linarith [bvc_L1_pos, bvc_L2_neg])
  linarith

theorem bvc_theorem_6 :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k₀ k₁ : ℝ),
        0 < k₀ → k₀ < 1 → 0 < k₁ → k₁ < 1 → Real.log (k₁ / k₀) = lamKappa0 n →
        ∀ s : Agent n G → Bool,
          (∀ e : G.edgeSet, act (vcNet G k₀ k₁) 1 (Agent.edg e) s = true) →
          act (vcNet G k₀ k₁) 0 Agent.kap s = false →
          ((∃ C : Finset (Fin n), G.IsVertexCover (C : Set (Fin n)) ∧
              (C.card : ℝ) ≤ 85 / 100 * n) →
            post (vcNet G k₀ k₁) true (infoSet (vcNet G k₀ k₁) 2 Agent.iAg s) <
              Real.exp (-(c * n))) ∧
          ((∀ C : Finset (Fin n), G.IsVertexCover (C : Set (Fin n)) →
              999 / 1000 * (n : ℝ) ≤ C.card) →
            post (vcNet G k₀ k₁) false (infoSet (vcNet G k₀ k₁) 2 Agent.iAg s) <
              Real.exp (-(c * n))) := by
  have hL1 := bvc_L1_pos
  have hL2 := bvc_L2_neg
  have hL12 := bvc_L12_pos
  set c0 : ℝ := (bvcL1 - bvcL2) / 2000 with hc0
  have hc0pos : 0 < c0 := div_pos (by linarith) (by norm_num)
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * Real.log 2 / c0)
  refine ⟨c0 / 2, by positivity, N + 1, ?_⟩
  intro n hn G _ k₀ k₁ hk₀ hk₀' hk₁ hk₁' hlam s hedg hkap
  classical
  have hn1 : 1 ≤ n := by omega
  have hnR : (N : ℝ) + 1 ≤ n := by exact_mod_cast hn
  have hq998 := bvc_qtil (998 / 1000)
  have hq999 := bvc_qtil (999 / 1000)
  have hlam' : lamKappa0 n = -((n : ℝ) / 2) * (qtil (998 / 1000) + qtil (999 / 1000)) := rfl
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hlamneg : lamKappa0 n < 0 := by
    rw [hlam', hq998, hq999]
    nlinarith
  have hκ : k₁ < k₀ := by
    have h1 : Real.log (k₁ / k₀) < 0 := hlam ▸ hlamneg
    have := (Real.log_neg_iff (div_pos hk₁ hk₀)).1 h1
    rwa [div_lt_one hk₀] at this
  have hk1 : k₁ = k₀ * Real.exp (lamKappa0 n) := by
    rw [← hlam, Real.exp_log (div_pos hk₁ hk₀)]; field_simp
  obtain ⟨hpt, hpf⟩ := bvc_post2 G k₀ k₁ hk₀ hk₀' hk₁ hk₁' hκ s hedg hkap
  have hA : 0 < bvcA n G (4 / 10) (6 / 10) := bvcA_pos n G _ _ (by norm_num) (by norm_num)
  have hB : 0 < bvcA n G (3 / 10) (7 / 10) := bvcA_pos n G _ _ (by norm_num) (by norm_num)
  have hE1 : lamKappa0 n + n * qtil (999 / 1000) = n * c0 := by
    rw [hlam', hq998, hq999, hc0]; ring
  have hE2 : lamKappa0 n + n * qtil (998 / 1000) = -(n * c0) := by
    rw [hlam', hq998, hq999, hc0]; ring
  have hbig : 2 * Real.exp (-(n * c0)) ≤ Real.exp (-(c0 / 2 * n)) := by
    have h1 : 2 * Real.log 2 < c0 * n := by
      have := (div_lt_iff₀ hc0pos).1 hN
      nlinarith
    calc 2 * Real.exp (-(n * c0)) = Real.exp (Real.log 2 + -(n * c0)) := by
          rw [Real.exp_add, Real.exp_log (by norm_num)]
      _ ≤ Real.exp (-(c0 / 2 * n)) := Real.exp_le_exp.2 (by nlinarith)
  have hmono : Real.exp (-(n * c0)) ≤ Real.exp (-(c0 / 2 * n)) :=
    Real.exp_le_exp.2 (by nlinarith)
  have hexp0 : 0 < Real.exp (-(c0 / 2 * n)) := Real.exp_pos _
  constructor
  · rintro ⟨Cs, hCs, hcard⟩
    rw [hpt]
    set E := Real.exp ((n : ℝ) * qtil (998 / 1000)) with hE
    have hEpos : 0 < E := Real.exp_pos _
    have hA_le : bvcA n G (4 / 10) (6 / 10) ≤ E * bvcA n G (3 / 10) (7 / 10) + (41 / 100) ^ n := by
      unfold bvcA
      rw [← Finset.sum_filter_add_sum_filter_not _
        (fun C : Finset (Fin n) => (C.card : ℝ) ≤ 998 / 1000 * n)]
      apply add_le_add
      · rw [mul_sum]
        calc _ ≤ ∑ C ∈ (univ.filter (fun C : Finset (Fin n) => G.IsVertexCover (C : Set (Fin n)))).filter
                (fun C : Finset (Fin n) => (C.card : ℝ) ≤ 998 / 1000 * n),
                E * ((3 / 10 : ℝ) ^ C.card * (7 / 10 : ℝ) ^ (n - C.card)) := by
              apply sum_le_sum
              intro C hC
              rw [mem_filter] at hC
              exact bvc_term_le n C.card (card_le_univ C |>.trans (by simp)) _ hC.2
          _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
                (fun _ _ _ => by positivity)
      · calc _ ≤ ∑ C ∈ univ.filter (fun C : Finset (Fin n) => 998 / 1000 * (n : ℝ) < C.card),
                (4 / 10 : ℝ) ^ C.card * (6 / 10 : ℝ) ^ (n - C.card) := by
              apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => by positivity)
              intro C hC
              simp only [mem_filter, mem_univ, true_and, not_le] at hC ⊢
              exact hC.2
          _ ≤ _ := (eq_16 n hn1).1.trans (eq_16 n hn1).2.le
    have hCsn : Cs.card ≤ n := card_le_univ Cs |>.trans (by simp)
    have hB_ge : (42 / 100 : ℝ) ^ n < E * bvcA n G (3 / 10) (7 / 10) := by
      calc (42 / 100 : ℝ) ^ n < (4 / 10 : ℝ) ^ Cs.card * (6 / 10 : ℝ) ^ (n - Cs.card) :=
            bvc_a_big n Cs.card hn1 hCsn hcard
        _ ≤ E * ((3 / 10 : ℝ) ^ Cs.card * (7 / 10 : ℝ) ^ (n - Cs.card)) :=
            bvc_term_le n Cs.card hCsn _ (by linarith)
        _ ≤ E * bvcA n G (3 / 10) (7 / 10) := by
            apply mul_le_mul_of_nonneg_left _ hEpos.le
            unfold bvcA
            apply single_le_sum (f := fun C : Finset (Fin n) =>
              (3 / 10 : ℝ) ^ C.card * (7 / 10 : ℝ) ^ (n - C.card)) (fun _ _ => by positivity)
            simpa using hCs
    have h41 : (41 / 100 : ℝ) ^ n ≤ (42 / 100) ^ n :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) n
    have hkey : k₁ * bvcA n G (4 / 10) (6 / 10) ≤
        2 * Real.exp (-(n * c0)) * (k₀ * bvcA n G (3 / 10) (7 / 10)) := by
      have h1 : Real.exp (lamKappa0 n) * E = Real.exp (-(n * c0)) := by
        rw [hE, ← Real.exp_add, hE2]
      calc k₁ * bvcA n G (4 / 10) (6 / 10)
          ≤ k₀ * Real.exp (lamKappa0 n) * (2 * (E * bvcA n G (3 / 10) (7 / 10))) := by
            rw [hk1]
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            linarith
        _ = 2 * (Real.exp (lamKappa0 n) * E) * (k₀ * bvcA n G (3 / 10) (7 / 10)) := by ring
        _ = _ := by rw [h1]
    rw [div_lt_iff₀ (add_pos (mul_pos hk₁ hA) (mul_pos hk₀ hB))]
    have h2 : 2 * Real.exp (-(n * c0)) * (k₀ * bvcA n G (3 / 10) (7 / 10)) ≤
        Real.exp (-(c0 / 2 * n)) * (k₀ * bvcA n G (3 / 10) (7 / 10)) :=
      mul_le_mul_of_nonneg_right hbig (by positivity)
    have h3 : 0 < Real.exp (-(c0 / 2 * n)) * (k₁ * bvcA n G (4 / 10) (6 / 10)) :=
      mul_pos hexp0 (mul_pos hk₁ hA)
    rw [mul_add]
    linarith
  · intro hNO
    rw [hpf]
    set E := Real.exp ((n : ℝ) * qtil (999 / 1000)) with hE
    have hAB : E * bvcA n G (3 / 10) (7 / 10) ≤ bvcA n G (4 / 10) (6 / 10) := by
      unfold bvcA
      rw [mul_sum]
      apply sum_le_sum
      intro C hC
      simp only [mem_filter, mem_univ, true_and] at hC
      exact bvc_term_ge n C.card (card_le_univ C |>.trans (by simp)) _ (hNO C hC)
    have hkey : k₀ * bvcA n G (3 / 10) (7 / 10) ≤
        Real.exp (-(n * c0)) * (k₁ * bvcA n G (4 / 10) (6 / 10)) := by
      have h1 : Real.exp (-(n * c0)) * (Real.exp (lamKappa0 n) * E) = 1 := by
        rw [hE, ← Real.exp_add, ← Real.exp_add, hE1]; simp
      calc k₀ * bvcA n G (3 / 10) (7 / 10)
          = Real.exp (-(n * c0)) * (k₀ * Real.exp (lamKappa0 n) *
              (E * bvcA n G (3 / 10) (7 / 10))) := by
            rw [show Real.exp (-(n * c0)) * (k₀ * Real.exp (lamKappa0 n) *
              (E * bvcA n G (3 / 10) (7 / 10))) = (Real.exp (-(n * c0)) *
                (Real.exp (lamKappa0 n) * E)) * (k₀ * bvcA n G (3 / 10) (7 / 10)) by ring, h1,
              one_mul]
        _ ≤ Real.exp (-(n * c0)) * (k₀ * Real.exp (lamKappa0 n) * bvcA n G (4 / 10) (6 / 10)) := by
            apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
            apply mul_le_mul_of_nonneg_left hAB (by positivity)
        _ = _ := by rw [hk1]
    rw [div_lt_iff₀ (add_pos (mul_pos hk₁ hA) (mul_pos hk₀ hB))]
    have h2 : Real.exp (-(n * c0)) * (k₁ * bvcA n G (4 / 10) (6 / 10)) ≤
        Real.exp (-(c0 / 2 * n)) * (k₁ * bvcA n G (4 / 10) (6 / 10)) :=
      mul_le_mul_of_nonneg_right hmono (by positivity)
    have h3 : 0 < Real.exp (-(c0 / 2 * n)) * (k₀ * bvcA n G (3 / 10) (7 / 10)) :=
      mul_pos hexp0 (mul_pos hk₀ hB)
    rw [mul_add]
    linarith

end BayesGroupHard.VertexCover

open BayesGroupHard.VertexCover in
theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k₀ k₁ : ℝ),
        0 < k₀ → k₀ < 1 → 0 < k₁ → k₁ < 1 → Real.log (k₁ / k₀) = lamKappa0 n →
        ∀ s : Agent n G → Bool,
          (∀ e : G.edgeSet, act (vcNet G k₀ k₁) 1 (Agent.edg e) s = true) →
          act (vcNet G k₀ k₁) 0 Agent.kap s = false →
          ((∃ C : Finset (Fin n), G.IsVertexCover (C : Set (Fin n)) ∧
              (C.card : ℝ) ≤ 85 / 100 * n) →
            post (vcNet G k₀ k₁) true (infoSet (vcNet G k₀ k₁) 2 Agent.iAg s) <
              Real.exp (-(c * n))) ∧
          ((∀ C : Finset (Fin n), G.IsVertexCover (C : Set (Fin n)) →
              999 / 1000 * (n : ℝ) ≤ C.card) →
            post (vcNet G k₀ k₁) false (infoSet (vcNet G k₀ k₁) 2 Agent.iAg s) <
              Real.exp (-(c * n))) :=
  BayesGroupHard.VertexCover.bvc_theorem_6

