-- Prove2me | solution 1 for CombOpt.TJoin.theorem_5_30
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-12T11:05:34.490348+00:00
-- url     : https://prove2.me/submissions/16b89be8-0718-44f2-bed9-d11d256c5dcc

import Mathlib
import Definitions.Def_CombOpt_TJoin_Graph
import Definitions.Def_CombOpt_TJoin_Graph_cut
import Definitions.Def_CombOpt_TJoin_Graph_IsTJoin
import Definitions.Def_CombOpt_TJoin_Graph_minTJoinCost
import Definitions.Def_CombOpt_TJoin_Graph_IsFeasible537
import Definitions.Def_CombOpt_TJoin_Graph_lpValue537
import Theorems.Thm_CombOpt_TJoin_theorem_5_28

set_option autoImplicit false

namespace CombOpt.TJoin.R530

open CombOpt.TJoin
open scoped symmDiff

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

set_option linter.unusedSectionVars false

lemma z2_add_self (z : ZMod 2) : z + z = 0 := by
  fin_cases z <;> decide

lemma card_symmDiff_z2 {α : Type*} [DecidableEq α] (A B : Finset α) :
    (((A ∆ B).card : ℕ) : ZMod 2) = (A.card : ZMod 2) + (B.card : ZMod 2) := by
  have h1 : (A ∆ B).card = (A \ B).card + (B \ A).card := by
    rw [symmDiff_def]
    exact Finset.card_union_of_disjoint disjoint_sdiff_sdiff
  have h2 := Finset.card_sdiff_add_card_inter A B
  have h3 := Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm] at h3
  rw [← h2, ← h3, h1]
  push_cast
  have := z2_add_self ((A ∩ B).card : ZMod 2)
  linear_combination -this

lemma mem_cut_iff (G : Graph V E) (S : Finset V) (e : E) (a b : V) (h : G.ends e = s(a, b)) :
    e ∈ G.cut S ↔ (a ∈ S ∧ b ∉ S) ∨ (b ∈ S ∧ a ∉ S) := by
  simp only [Graph.cut, Finset.mem_filter, Finset.mem_univ, true_and, h, Sym2.mem_iff,
    Finset.mem_compl]
  constructor
  · rintro ⟨⟨x, hx, rfl | rfl⟩, ⟨y, hy, rfl | rfl⟩⟩ <;> tauto
  · rintro (⟨ha, hb⟩ | ⟨hb, ha⟩)
    · exact ⟨⟨a, ha, Or.inl rfl⟩, ⟨b, hb, Or.inr rfl⟩⟩
    · exact ⟨⟨b, hb, Or.inr rfl⟩, ⟨a, ha, Or.inl rfl⟩⟩

lemma filter_cut_single_z2 (G : Graph V E) (S : Finset V) (e : E) :
    (((S.filter (fun v => e ∈ G.cut {v})).card : ℕ) : ZMod 2) =
      if e ∈ G.cut S then 1 else 0 := by
  obtain ⟨⟨a, b⟩, hab⟩ := Quot.exists_rep (G.ends e)
  have h : G.ends e = s(a, b) := hab.symm
  by_cases hd : a = b
  · subst hd
    have : S.filter (fun v => e ∈ G.cut {v}) = ∅ := by
      ext v
      simp [mem_cut_iff G _ e a a h]
    rw [this]
    simp [mem_cut_iff G S e a a h]
  · have hf : S.filter (fun v => e ∈ G.cut {v}) = ({a, b} : Finset V).filter (· ∈ S) := by
      ext v
      simp only [Finset.mem_filter, mem_cut_iff G _ e a b h, Finset.mem_singleton,
        Finset.mem_insert]
      constructor
      · rintro ⟨hv, (⟨rfl, -⟩ | ⟨rfl, -⟩)⟩ <;> tauto
      · rintro ⟨(rfl | rfl), hv⟩
        · exact ⟨hv, Or.inl ⟨rfl, fun h' => hd h'.symm⟩⟩
        · exact ⟨hv, Or.inr ⟨rfl, hd⟩⟩
    rw [hf, Finset.card_filter, Finset.sum_pair hd]
    simp only [mem_cut_iff G S e a b h]
    by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> simp [ha, hb] <;> decide

lemma cut_card_z2 (G : Graph V E) (J : Finset E) (S : Finset V) :
    (((J ∩ G.cut S).card : ℕ) : ZMod 2) = ∑ v ∈ S, (((J ∩ G.cut {v}).card : ℕ) : ZMod 2) := by
  have key : ∀ A : Finset V, (J ∩ G.cut A).card = ∑ e ∈ J, if e ∈ G.cut A then 1 else 0 := by
    intro A
    rw [← Finset.card_filter, Finset.filter_mem_eq_inter]
  simp_rw [key]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← filter_cut_single_z2 G S e, Finset.card_filter]
  push_cast
  rfl

lemma isTJoin_iff_z2 (G : Graph V E) (A : Finset V) (J : Finset E) :
    G.IsTJoin A J ↔ ∀ v, (((J ∩ G.cut {v}).card : ℕ) : ZMod 2) = (((A ∩ {v}).card : ℕ) : ZMod 2) := by
  unfold Graph.IsTJoin
  simp only [ZMod.natCast_eq_natCast_iff]

lemma sum_inter_single (S A : Finset V) :
    ∑ v ∈ S, (((A ∩ {v}).card : ℕ) : ZMod 2) = (((S ∩ A).card : ℕ) : ZMod 2) := by
  have : ∀ v, (A ∩ {v}).card = if v ∈ A then 1 else 0 := by
    intro v
    by_cases hv : v ∈ A
    · simp [Finset.inter_singleton_of_mem hv, hv]
    · simp [Finset.inter_singleton_of_notMem hv, hv]
  simp_rw [this]
  rw [← Finset.filter_mem_eq_inter, Finset.card_filter]
  push_cast
  rfl

lemma isTJoin_cut (G : Graph V E) (A : Finset V) (J : Finset E) (hJ : G.IsTJoin A J)
    (S : Finset V) : (((J ∩ G.cut S).card : ℕ) : ZMod 2) = (((S ∩ A).card : ℕ) : ZMod 2) := by
  rw [cut_card_z2, ← sum_inter_single]
  exact Finset.sum_congr rfl fun v _ => (isTJoin_iff_z2 G A J).1 hJ v

/-- The odd-degree vertex set of an edge set. -/
def bd (G : Graph V E) (N : Finset E) : Finset V :=
  Finset.univ.filter (fun v => Odd (N ∩ G.cut {v}).card)

lemma isTJoin_bd (G : Graph V E) (N : Finset E) : G.IsTJoin (bd G N) N := by
  intro v
  by_cases h : Odd (N ∩ G.cut {v}).card
  · have hv : v ∈ bd G N := by simp [bd, h]
    rw [Finset.inter_singleton_of_mem hv, Finset.card_singleton]
    exact Nat.odd_iff.mp h
  · have hv : v ∉ bd G N := by simp [bd, h]
    rw [Finset.inter_singleton_of_notMem hv, Finset.card_empty]
    exact Nat.even_iff.mp (Nat.not_odd_iff_even.mp h)

lemma inter_symmDiff {α : Type*} [DecidableEq α] (A B C : Finset α) :
    (A ∆ B) ∩ C = (A ∩ C) ∆ (B ∩ C) := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_symmDiff]
  tauto

lemma flip_isTJoin (G : Graph V E) (A : Finset V) (J N : Finset E) (hJ : G.IsTJoin A J) :
    G.IsTJoin (A ∆ bd G N) (J ∆ N) := by
  rw [isTJoin_iff_z2] at hJ ⊢
  have hN := (isTJoin_iff_z2 G _ N).1 (isTJoin_bd G N)
  intro v
  rw [inter_symmDiff, inter_symmDiff, card_symmDiff_z2, card_symmDiff_z2, hJ v, hN v]

lemma cut_univ (G : Graph V E) : G.cut Finset.univ = ∅ := by
  ext e
  simp [Graph.cut]

lemma even_flip (G : Graph V E) (T : Finset V) (hT : Even T.card) (N : Finset E) :
    Even (T ∆ bd G N).card := by
  rw [← ZMod.natCast_eq_zero_iff_even, card_symmDiff_z2, (ZMod.natCast_eq_zero_iff_even).2 hT]
  have := isTJoin_cut G _ N (isTJoin_bd G N) Finset.univ
  rw [cut_univ, Finset.inter_empty, Finset.univ_inter] at this
  rw [← this]
  simp

lemma sum_univ_ite (s : Finset E) (f : E → ℝ) :
    ∑ e ∈ s, f e = ∑ e, if e ∈ s then f e else 0 := by
  rw [← Finset.sum_filter]
  simp

/-- Cost identity under the flip by the negative edges. -/
lemma cost_flip (c : E → ℝ) (J : Finset E) :
    ∑ e ∈ J, c e = ∑ e ∈ J ∆ Finset.univ.filter (fun e => c e < 0), |c e|
      + ∑ e ∈ Finset.univ.filter (fun e => c e < 0), c e := by
  rw [sum_univ_ite J, sum_univ_ite (J ∆ _), sum_univ_ite (Finset.univ.filter _),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases hc : c e < 0 <;> by_cases hJ : e ∈ J <;>
    simp [Finset.mem_symmDiff, hc, hJ, abs_of_neg, abs_of_nonneg, le_of_not_gt]

/-- LP cost identity under the flip. -/
lemma lpcost_flip (c x : E → ℝ) :
    ∑ e, c e * x e = ∑ e, |c e| * (if c e < 0 then 1 - x e else x e)
      + ∑ e ∈ Finset.univ.filter (fun e => c e < 0), c e := by
  rw [Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases hc : c e < 0
  · simp only [hc, if_true, abs_of_neg hc]
    ring
  · simp only [hc, if_false, abs_of_nonneg (le_of_not_gt hc)]
    ring

lemma charVec_feasible (G : Graph V E) (T : Finset V) (J : Finset E) (hJ : G.IsTJoin T J) :
    G.IsFeasible537 T (fun e => if e ∈ J then 1 else 0) := by
  refine ⟨fun S F hF hodd => ?_, fun e => by by_cases h : e ∈ J <;> simp [h]⟩
  have hsF : ∑ e ∈ F, (if e ∈ J then (1 : ℝ) else 0) = ((F.filter (· ∈ J)).card : ℝ) := by
    rw [Finset.sum_boole]
  have hsC : 0 ≤ ∑ e ∈ G.cut S \ F, (if e ∈ J then (1 : ℝ) else 0) :=
    Finset.sum_nonneg fun e _ => by by_cases h : e ∈ J <;> simp [h]
  have hle : (F.filter (· ∈ J)).card ≤ F.card := Finset.card_filter_le _ _
  by_cases h1 : ∃ e ∈ G.cut S \ F, e ∈ J
  · obtain ⟨e, he, heJ⟩ := h1
    have : (1 : ℝ) ≤ ∑ e ∈ G.cut S \ F, (if e ∈ J then (1 : ℝ) else 0) := by
      have := Finset.single_le_sum (f := fun e => if e ∈ J then (1 : ℝ) else 0)
        (fun e _ => by by_cases h : e ∈ J <;> simp [h]) he
      simpa [heJ] using this
    have : ((F.filter (· ∈ J)).card : ℝ) ≤ F.card := by exact_mod_cast hle
    linarith
  by_cases h2 : ∃ e ∈ F, e ∉ J
  · have hlt : (F.filter (· ∈ J)).card < F.card :=
      Finset.card_lt_card (Finset.filter_ssubset.2 h2)
    have : ((F.filter (· ∈ J)).card : ℝ) + 1 ≤ F.card := by exact_mod_cast hlt
    linarith
  exfalso
  push Not at h1 h2
  have hJF : J ∩ G.cut S = F := by
    ext e
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨heJ, heC⟩
      by_contra hF'
      exact h1 e (Finset.mem_sdiff.2 ⟨heC, hF'⟩) heJ
    · intro heF
      exact ⟨h2 e heF, hF heF⟩
  have hp := isTJoin_cut G T J hJ S
  rw [hJF] at hp
  have ho := (ZMod.natCast_eq_one_iff_odd).2 hodd
  push_cast at ho
  rw [← hp, z2_add_self] at ho
  exact zero_ne_one ho

lemma flip_feasible (G : Graph V E) (T : Finset V) (c x : E → ℝ)
    (hx : G.IsFeasible537 T x) :
    G.IsFeasible533 (T ∆ bd G (Finset.univ.filter (fun e => c e < 0)))
      (fun e => if c e < 0 then 1 - x e else x e) := by
  set N := Finset.univ.filter (fun e => c e < 0) with hNdef
  refine ⟨fun S hS => ?_, fun e => ?_⟩
  · set F := N ∩ G.cut S with hFdef
    have hFsub : F ⊆ G.cut S := Finset.inter_subset_right
    have hodd : Odd (F.card + (S ∩ T).card) := by
      rw [← ZMod.natCast_eq_one_iff_odd] at hS ⊢
      push_cast
      rw [isTJoin_cut G _ N (isTJoin_bd G N) S]
      rw [Finset.inter_comm S, inter_symmDiff, card_symmDiff_z2] at hS
      rw [Finset.inter_comm S T, Finset.inter_comm S]
      rw [← hS]
      ring
    have hc := hx.1 S F hFsub hodd
    rw [← Finset.sum_sdiff hFsub]
    have e1 : ∑ e ∈ G.cut S \ F, (if c e < 0 then 1 - x e else x e) = ∑ e ∈ G.cut S \ F, x e := by
      refine Finset.sum_congr rfl fun e he => ?_
      have : ¬ c e < 0 := by
        intro hce
        have hm := Finset.mem_sdiff.1 he
        exact hm.2 (Finset.mem_inter.2 ⟨by simp [hNdef, hce], hm.1⟩)
      simp [this]
    have e2 : ∑ e ∈ F, (if c e < 0 then 1 - x e else x e) = ∑ e ∈ F, (1 - x e) := by
      refine Finset.sum_congr rfl fun e he => ?_
      have : c e < 0 := by
        have := (Finset.mem_inter.1 he).1
        simpa [hNdef] using this
      simp [this]
    rw [e1, e2, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    linarith
  · by_cases h : c e < 0 <;> simp [h, (hx.2 e).1, (hx.2 e).2]

/-- Theorem 5.30 from Theorem 5.28 (given as a hypothesis). -/
theorem main
    (h528 : ∀ (T' : Finset V), Even T'.card → ∀ (c' : E → ℝ), (∀ e, 0 ≤ c' e) →
      ∀ (G : Graph V E), G.minTJoinCost T' c' = G.lpValue533 T' c')
    (G : Graph V E) (T : Finset V) (hT : Even T.card) (c : E → ℝ) :
    G.minTJoinCost T c = G.lpValue537 T c := by
  set N := Finset.univ.filter (fun e => c e < 0) with hNdef
  set K : ℝ := ∑ e ∈ N, c e with hK
  set T' := T ∆ bd G N with hT'
  have hT'e : Even T'.card := even_flip G T hT N
  have h5 := h528 T' hT'e (fun e => |c e|) (fun e => abs_nonneg _) G
  apply le_antisymm
  · -- min ≤ LP
    refine le_iInf₂ fun x hx => ?_
    -- min T c + (-K) ≤ min T' |c|
    have hA : G.minTJoinCost T c + ((-K : ℝ) : EReal) ≤ G.minTJoinCost T' (fun e => |c e|) := by
      refine le_iInf₂ fun J' hJ' => ?_
      have hJ : G.IsTJoin T (J' ∆ N) := by
        have := flip_isTJoin G T' J' N hJ'
        rwa [hT', symmDiff_symmDiff_cancel_right] at this
      have hle : G.minTJoinCost T c ≤ ((∑ e ∈ J' ∆ N, c e : ℝ) : EReal) := iInf₂_le _ hJ
      have hcost := cost_flip c (J' ∆ N)
      rw [← hNdef, symmDiff_symmDiff_cancel_right] at hcost
      calc G.minTJoinCost T c + ((-K : ℝ) : EReal)
          ≤ ((∑ e ∈ J' ∆ N, c e : ℝ) : EReal) + ((-K : ℝ) : EReal) := by gcongr
        _ = ((∑ e ∈ J', |c e| : ℝ) : EReal) := by
          rw [← EReal.coe_add, hcost]
          congr 1
          rw [hK]
          ring
    have hB : G.lpValue533 T' (fun e => |c e|) ≤
        ((∑ e, |c e| * (if c e < 0 then 1 - x e else x e) : ℝ) : EReal) :=
      iInf₂_le _ (flip_feasible G T c x hx)
    have hC := (hA.trans h5.le).trans hB
    have hcx := lpcost_flip c x
    rw [← hNdef, ← hK] at hcx
    rw [hcx]
    generalize G.minTJoinCost T c = m at hC ⊢
    induction m using EReal.rec with
    | bot => exact bot_le
    | top =>
      rw [EReal.top_add_coe] at hC
      exact absurd hC (by simp)
    | coe m =>
      rw [← EReal.coe_add] at hC
      have := EReal.coe_le_coe_iff.1 hC
      exact EReal.coe_le_coe_iff.2 (by linarith)
  · -- LP ≤ min
    refine le_iInf₂ fun J hJ => ?_
    refine (iInf₂_le (fun e => if e ∈ J then (1 : ℝ) else 0) (charVec_feasible G T J hJ)).trans ?_
    apply le_of_eq
    congr 1
    simp [Finset.sum_ite_mem, mul_ite]

end CombOpt.TJoin.R530

open CombOpt.TJoin in
theorem solution {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : CombOpt.TJoin.Graph V E) (T : Finset V) (hT : Even T.card) (c : E → ℝ) :
    G.minTJoinCost T c = G.lpValue537 T c := by
  exact CombOpt.TJoin.R530.main
    (fun T' hT' c' hc' G' => CombOpt.TJoin.theorem_5_28 G' T' hT' c' hc') G T hT c
