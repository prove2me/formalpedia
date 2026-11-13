-- Prove2me | solution 1 for CombOpt.TJoin.theorem_5_28
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-12T10:47:48.772492+00:00
-- url     : https://prove2.me/submissions/2eee45b0-e481-4cce-b752-702d48d26a46

import Mathlib
import Definitions.Def_CombOpt_TJoin_Graph
import Definitions.Def_CombOpt_TJoin_Graph_cut
import Definitions.Def_CombOpt_TJoin_Graph_IsTJoin
import Definitions.Def_CombOpt_TJoin_Graph_minTJoinCost
import Definitions.Def_CombOpt_TJoin_Graph_IsFeasible533
import Definitions.Def_CombOpt_TJoin_Graph_lpValue533

set_option autoImplicit false

namespace CombOpt.TJoin.R528

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


/-- The characteristic vector of a T-join is feasible for (5.33): every T-cut meets J oddly. -/
lemma charVec_feasible533 (G : Graph V E) (T : Finset V) (J : Finset E) (hJ : G.IsTJoin T J) :
    G.IsFeasible533 T (fun e => if e ∈ J then 1 else 0) := by
  refine ⟨fun S hodd => ?_, fun e => by by_cases h : e ∈ J <;> simp [h]⟩
  have hs : ∑ e ∈ G.cut S, (if e ∈ J then (1 : ℝ) else 0) = ((J ∩ G.cut S).card : ℝ) := by
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_comm]
  rw [hs]
  have hp := isTJoin_cut G T J hJ S
  have ho : (((S ∩ T).card : ℕ) : ZMod 2) = 1 := (ZMod.natCast_eq_one_iff_odd).2 hodd
  rw [ho] at hp
  have hne : (J ∩ G.cut S).card ≠ 0 := by
    intro h0
    rw [h0] at hp
    simp at hp
  have : 1 ≤ (J ∩ G.cut S).card := Nat.one_le_iff_ne_zero.2 hne
  exact_mod_cast this

lemma lp_cost_charVec (c : E → ℝ) (J : Finset E) :
    ∑ e, c e * (if e ∈ J then (1 : ℝ) else 0) = ∑ e ∈ J, c e := by
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- The hard half (Edmonds–Johnson): every feasible point of (5.33) dominates, in cost, a T-join. -/
def KeyDom (G : Graph V E) (T : Finset V) (c : E → ℝ) : Prop :=
  ∀ x : E → ℝ, G.IsFeasible533 T x → ∃ J : Finset E, G.IsTJoin T J ∧ ∑ e ∈ J, c e ≤ ∑ e, c e * x e

/-- Assembly: the theorem from the key domination lemma. -/
theorem main (G : Graph V E) (T : Finset V) (c : E → ℝ) (key : KeyDom G T c) :
    G.minTJoinCost T c = G.lpValue533 T c := by
  unfold Graph.minTJoinCost Graph.lpValue533
  apply le_antisymm
  · refine le_iInf₂ fun x hx => ?_
    obtain ⟨J, hJ, hle⟩ := key x hx
    exact (iInf₂_le J hJ).trans (EReal.coe_le_coe_iff.2 hle)
  · refine le_iInf₂ fun J hJ => ?_
    calc _ ≤ ((∑ e, c e * (if e ∈ J then (1 : ℝ) else 0) : ℝ) : EReal) :=
          iInf₂_le (fun e => if e ∈ J then (1 : ℝ) else 0) (charVec_feasible533 G T J hJ)
      _ = _ := by rw [lp_cost_charVec]

-- ===== L1: an edge set meeting every T-cut contains a T-join =====
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

/-- `F` meets every `T`-cut. -/
def Covers (G : Graph V E) (T : Finset V) (F : Finset E) : Prop :=
  ∀ S : Finset V, Odd (S ∩ T).card → (F ∩ G.cut S).Nonempty

lemma cut_symmDiff (G : Graph V E) (R S : Finset V) : G.cut (R ∆ S) = G.cut R ∆ G.cut S := by
  ext e
  obtain ⟨⟨a, b⟩, hab⟩ := Quot.exists_rep (G.ends e)
  have h : G.ends e = s(a, b) := hab.symm
  simp only [Finset.mem_symmDiff, mem_cut_iff G _ e a b h]
  tauto

lemma odd_iff_z2 (n : ℕ) : Odd n ↔ ((n : ℕ) : ZMod 2) = 1 := (ZMod.natCast_eq_one_iff_odd).symm

lemma single_cut_z2 (G : Graph V E) (e : E) (R : Finset V) :
    (((R ∩ bd G {e}).card : ℕ) : ZMod 2) = if e ∈ G.cut R then 1 else 0 := by
  rw [← isTJoin_cut G _ {e} (isTJoin_bd G {e}) R]
  by_cases h : e ∈ G.cut R
  · rw [Finset.singleton_inter_of_mem h]; simp [h]
  · rw [Finset.singleton_inter_of_notMem h]; simp [h]

lemma inter_symmDiff_left {α : Type*} [DecidableEq α] (A B C : Finset α) :
    A ∩ (B ∆ C) = (A ∩ B) ∆ (A ∩ C) := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_symmDiff]
  tauto

theorem covers_exists_tjoin (G : Graph V E) :
    ∀ (F : Finset E) (T : Finset V), Covers G T F → ∃ J ⊆ F, G.IsTJoin T J := by
  intro F
  induction F using Finset.strongInduction with
  | H F ih =>
  intro T hF
  rcases F.eq_empty_or_nonempty with rfl | ⟨e, he⟩
  · refine ⟨∅, subset_refl _, ?_⟩
    intro v
    by_cases hv : v ∈ T
    · exfalso
      obtain ⟨f, hf⟩ := hF {v} (by
        rw [Finset.singleton_inter_of_mem hv, Finset.card_singleton]; exact odd_one)
      simp at hf
    · rw [Finset.inter_singleton_of_notMem hv]
      simp [Nat.ModEq]
  · have hlt : F.erase e ⊂ F := Finset.erase_ssubset he
    by_cases hc : Covers G T (F.erase e)
    · obtain ⟨J, hJ, hJT⟩ := ih _ hlt T hc
      exact ⟨J, hJ.trans (Finset.erase_subset e F), hJT⟩
    · simp only [Covers, not_forall, Finset.not_nonempty_iff_eq_empty] at hc
      obtain ⟨S, hS, hS0⟩ := hc
      have heS : e ∈ G.cut S := by
        obtain ⟨g, hg⟩ := hF S hS
        by_contra hne
        rw [Finset.mem_inter] at hg
        have hg' : g ∈ F.erase e ∩ G.cut S :=
          Finset.mem_inter.2 ⟨Finset.mem_erase.2 ⟨fun h => hne (by rw [← h]; exact hg.2), hg.1⟩, hg.2⟩
        rw [hS0] at hg'
        simp at hg'
      have hc' : Covers G (T ∆ bd G {e}) (F.erase e) := by
        intro R hR
        by_cases heR : e ∈ G.cut R
        · have h1 : (((R ∩ T).card : ℕ) : ZMod 2) = 0 := by
            have := (odd_iff_z2 _).1 hR
            rw [inter_symmDiff_left, card_symmDiff_z2, single_cut_z2, if_pos heR] at this
            linear_combination this
          have h2 : (((S ∩ T).card : ℕ) : ZMod 2) = 1 := (odd_iff_z2 _).1 hS
          have hodd : Odd ((R ∆ S) ∩ T).card := by
            rw [odd_iff_z2, inter_symmDiff, card_symmDiff_z2, h1, h2, zero_add]
          obtain ⟨f, hf⟩ := hF _ hodd
          rw [Finset.mem_inter, cut_symmDiff, Finset.mem_symmDiff] at hf
          rcases hf with ⟨hfF, ⟨hfR, hfS⟩ | ⟨hfS, hfR⟩⟩
          · exact ⟨f, Finset.mem_inter.2
              ⟨Finset.mem_erase.2 ⟨fun h => hfS (by rw [h]; exact heS), hfF⟩, hfR⟩⟩
          · exfalso
            have : f ∈ F.erase e ∩ G.cut S :=
              Finset.mem_inter.2 ⟨Finset.mem_erase.2 ⟨fun h => hfR (by rw [h]; exact heR), hfF⟩, hfS⟩
            rw [hS0] at this
            simp at this
        · have h1 : (((R ∩ T).card : ℕ) : ZMod 2) = 1 := by
            have := (odd_iff_z2 _).1 hR
            rw [inter_symmDiff_left, card_symmDiff_z2, single_cut_z2, if_neg heR, add_zero] at this
            exact this
          obtain ⟨f, hf⟩ := hF R ((odd_iff_z2 _).2 h1)
          rw [Finset.mem_inter] at hf
          exact ⟨f, Finset.mem_inter.2
            ⟨Finset.mem_erase.2 ⟨fun h => heR (by rw [← h]; exact hf.2), hf.1⟩, hf.2⟩⟩
      obtain ⟨J', hJ'F, hJ'⟩ := ih _ hlt _ hc'
      refine ⟨J' ∆ {e}, ?_, ?_⟩
      · intro f hf
        rw [Finset.mem_symmDiff] at hf
        rcases hf with ⟨hf1, -⟩ | ⟨hf2, -⟩
        · exact Finset.mem_of_mem_erase (hJ'F hf1)
        · rw [Finset.mem_singleton.1 hf2]; exact he
      · have := flip_isTJoin G (T ∆ bd G {e}) J' {e} hJ'
        rwa [symmDiff_symmDiff_cancel_right] at this

-- ===== L3: truncation + Krein–Milman: KeyDom from integrality of the extreme points of Q =====
/-- The bounded T-cut polytope `Q = {x ∈ [0,1]^E : x(δ(S)) ≥ 1 for T-odd S}`. -/
def Q (G : Graph V E) (T : Finset V) : Set (E → ℝ) := {x | G.IsFeasible533 T x ∧ ∀ e, x e ≤ 1}

lemma Q_convex (G : Graph V E) (T : Finset V) : Convex ℝ (Q G T) := by
  intro x hx y hy a b ha hb hab
  refine ⟨⟨fun S hS => ?_, fun e => ?_⟩, fun e => ?_⟩
  · have h1 := hx.1.1 S hS
    have h2 := hy.1.1 S hS
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    nlinarith [mul_nonneg ha (sub_nonneg.2 h1), mul_nonneg hb (sub_nonneg.2 h2)]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx.1.2 e)) (mul_nonneg hb (hy.1.2 e))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [mul_nonneg ha (sub_nonneg.2 (hx.2 e)), mul_nonneg hb (sub_nonneg.2 (hy.2 e))]

lemma Q_isClosed (G : Graph V E) (T : Finset V) : IsClosed (Q G T) := by
  have : Q G T = ((⋂ S : Finset V, {x : E → ℝ | Odd (S ∩ T).card → 1 ≤ ∑ e ∈ G.cut S, x e}) ∩
      (⋂ e : E, {x : E → ℝ | 0 ≤ x e})) ∩ (⋂ e : E, {x : E → ℝ | x e ≤ 1}) := by
    ext x
    simp only [Q, Graph.IsFeasible533, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [this]
  refine ((isClosed_iInter fun S => ?_).inter (isClosed_iInter fun e => ?_)).inter
    (isClosed_iInter fun e => ?_)
  · by_cases h : Odd (S ∩ T).card
    · simp only [h, true_implies]
      exact isClosed_le continuous_const (continuous_finset_sum _ fun e _ => continuous_apply e)
    · simp only [h, false_implies, Set.setOf_true]
      exact isClosed_univ
  · exact isClosed_le continuous_const (continuous_apply e)
  · exact isClosed_le (continuous_apply e) continuous_const

lemma Q_isCompact (G : Graph V E) (T : Finset V) : IsCompact (Q G T) := by
  have hK : IsCompact (Set.pi Set.univ fun _ : E => Set.Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  refine hK.of_isClosed_subset (Q_isClosed G T) ?_
  intro x hx
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies]
  exact fun e => ⟨hx.1.2 e, hx.2 e⟩

lemma trunc_mem (G : Graph V E) (T : Finset V) (x : E → ℝ) (hx : G.IsFeasible533 T x) :
    (fun e => min (x e) 1) ∈ Q G T := by
  refine ⟨⟨fun S hS => ?_, fun e => le_min (hx.2 e) zero_le_one⟩, fun e => min_le_right _ _⟩
  by_cases h : ∃ e ∈ G.cut S, 1 ≤ x e
  · obtain ⟨e, he, h1⟩ := h
    calc (1 : ℝ) = min (x e) 1 := (min_eq_right h1).symm
      _ ≤ ∑ e ∈ G.cut S, min (x e) 1 :=
        Finset.single_le_sum (f := fun e => min (x e) 1)
          (fun i _ => le_min (hx.2 i) zero_le_one) he
  · push Not at h
    have : ∑ e ∈ G.cut S, min (x e) 1 = ∑ e ∈ G.cut S, x e :=
      Finset.sum_congr rfl fun e he => min_eq_left (h e he).le
    rw [this]
    exact hx.1 S hS

theorem keyDom_of_extreme (G : Graph V E) (T : Finset V) (c : E → ℝ) (hc : ∀ e, 0 ≤ c e)
    (hext : ∀ x ∈ (Q G T).extremePoints ℝ,
      ∃ F : Finset E, x = fun e => if e ∈ F then (1 : ℝ) else 0) :
    KeyDom G T c := by
  classical
  intro x hx
  have hx'Q : (fun e => min (x e) 1) ∈ Q G T := trunc_mem G T x hx
  have hcost : ∑ e, c e * min (x e) 1 ≤ ∑ e, c e * x e :=
    Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (min_le_left _ _) (hc e)
  have hdom : ∀ y ∈ (Q G T).extremePoints ℝ,
      ∃ J, G.IsTJoin T J ∧ ∑ e ∈ J, c e ≤ ∑ e, c e * y e := by
    intro y hy
    obtain ⟨F, rfl⟩ := hext y hy
    have hyQ := hy.1
    have hcov : Covers G T F := by
      intro S hS
      have h1 := hyQ.1.1 S hS
      beta_reduce at h1
      rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_comm] at h1
      rw [Finset.nonempty_iff_ne_empty]
      intro h0
      rw [h0] at h1
      norm_num at h1
    obtain ⟨J, hJF, hJ⟩ := covers_exists_tjoin G F T hcov
    refine ⟨J, hJ, ?_⟩
    show ∑ e ∈ J, c e ≤ ∑ e, c e * (if e ∈ F then (1 : ℝ) else 0)
    rw [lp_cost_charVec]
    exact Finset.sum_le_sum_of_subset_of_nonneg hJF fun e _ _ => hc e
  obtain ⟨y0, hy0⟩ := (Q_isCompact G T).extremePoints_nonempty ⟨_, hx'Q⟩
  obtain ⟨J0, hJ0, -⟩ := hdom y0 hy0
  have hne : (Finset.univ.filter (fun J : Finset E => G.IsTJoin T J)).Nonempty :=
    ⟨J0, by simp [hJ0]⟩
  obtain ⟨Js, hJs, hmin⟩ := Finset.exists_min_image _ (fun J : Finset E => ∑ e ∈ J, c e) hne
  have hJsT : G.IsTJoin T Js := by simpa using hJs
  set H : Set (E → ℝ) := {y | ∑ e ∈ Js, c e ≤ ∑ e, c e * y e} with hH
  have hlin : IsLinearMap ℝ (fun y : E → ℝ => ∑ e, c e * y e) :=
    ⟨fun a b => by simp [mul_add, Finset.sum_add_distrib],
     fun r a => by simp [Finset.mul_sum, mul_left_comm]⟩
  have hHconv : Convex ℝ H := convex_halfSpace_ge hlin _
  have hHcl : IsClosed H :=
    isClosed_le continuous_const
      (continuous_finset_sum _ fun e _ => continuous_const.mul (continuous_apply e))
  have hsub : (Q G T).extremePoints ℝ ⊆ H := by
    intro y hy
    obtain ⟨J, hJ, hle⟩ := hdom y hy
    exact (hmin J (by simp [hJ])).trans hle
  have hQ : Q G T ⊆ H := by
    rw [← closure_convexHull_extremePoints (Q_isCompact G T) (Q_convex G T)]
    exact closure_minimal (convexHull_min hsub hHconv) hHcl
  exact ⟨Js, hJsT, (hQ hx'Q).trans hcost⟩

-- ===== L4 infrastructure: contraction of S to s0 inside the same vertex type =====
def collapse (S : Finset V) (s0 : V) (v : V) : V := if v ∈ S then s0 else v

def contr (G : Graph V E) (S : Finset V) (s0 : V) : Graph V E :=
  ⟨fun e => (G.ends e).map (collapse S s0)⟩

def contrT (T S : Finset V) (s0 : V) : Finset V :=
  (T \ S) ∪ (if Odd (S ∩ T).card then {s0} else ∅)

def pre (S : Finset V) (s0 : V) (R : Finset V) : Finset V :=
  Finset.univ.filter (fun v => collapse S s0 v ∈ R)

lemma mem_pre (S : Finset V) (s0 : V) (R : Finset V) (v : V) :
    v ∈ pre S s0 R ↔ (if v ∈ S then s0 ∈ R else v ∈ R) := by
  unfold pre
  first
    | rw [Finset.mem_filter_univ]
    | (rw [Finset.mem_filter]; simp only [Finset.mem_univ, true_and])
  unfold collapse
  split_ifs <;> rfl

lemma contr_cut (G : Graph V E) (S : Finset V) (s0 : V) (R : Finset V) :
    (contr G S s0).cut R = G.cut (pre S s0 R) := by
  ext e
  obtain ⟨⟨a, b⟩, hab⟩ := Quot.exists_rep (G.ends e)
  have h : G.ends e = s(a, b) := hab.symm
  have h1 : (contr G S s0).ends e = s(collapse S s0 a, collapse S s0 b) := by
    simp [contr, h]
  rw [mem_cut_iff _ _ e _ _ h1, mem_cut_iff G _ e a b h, mem_pre, mem_pre]
  simp only [collapse]
  split_ifs <;> tauto

lemma pre_inter_card_z2 (S T R : Finset V) (s0 : V) (hs0 : s0 ∈ S) :
    (((pre S s0 R ∩ T).card : ℕ) : ZMod 2) = (((R ∩ contrT T S s0).card : ℕ) : ZMod 2) := by
  have hA : pre S s0 R ∩ T = ((R \ S) ∩ T) ∪ (if s0 ∈ R then S ∩ T else ∅) := by
    ext v
    by_cases hv : v ∈ S <;> by_cases hr : s0 ∈ R <;>
      simp only [Finset.mem_inter, mem_pre, Finset.mem_union, Finset.mem_sdiff, hv, hr, if_true,
        if_false, Finset.notMem_empty] <;> tauto
  have hdA : Disjoint ((R \ S) ∩ T) (if s0 ∈ R then S ∩ T else ∅) := by
    split_ifs
    · rw [Finset.disjoint_left]
      intro v hv hv'
      simp only [Finset.mem_inter, Finset.mem_sdiff] at hv hv'
      exact hv.1.2 hv'.1
    · exact Finset.disjoint_empty_right _
  by_cases ho : Odd (S ∩ T).card
  · have hB : R ∩ contrT T S s0 = ((R \ S) ∩ T) ∪ (if s0 ∈ R then {s0} else ∅) := by
      ext v
      by_cases hv : v = s0
      · subst hv
        by_cases hr : v ∈ R <;> simp [contrT, ho, hr, hs0]
      · by_cases hr : s0 ∈ R <;> simp [contrT, ho, hr, hv] <;> tauto
    have hdB : Disjoint ((R \ S) ∩ T) (if s0 ∈ R then {s0} else ∅) := by
      split_ifs
      · rw [Finset.disjoint_singleton_right]
        simp [hs0]
      · exact Finset.disjoint_empty_right _
    rw [hA, hB, Finset.card_union_of_disjoint hdA, Finset.card_union_of_disjoint hdB]
    push_cast
    congr 1
    split_ifs
    · rw [(odd_iff_z2 _).1 ho]; simp
    · simp
  · have hB : R ∩ contrT T S s0 = (R \ S) ∩ T := by
      ext v
      by_cases hv : v ∈ S <;> simp [contrT, ho, hv] <;> tauto
    rw [hA, hB, Finset.card_union_of_disjoint hdA]
    push_cast
    have he : (((S ∩ T).card : ℕ) : ZMod 2) = 0 :=
      (ZMod.natCast_eq_zero_iff_even).2 (Nat.not_odd_iff_even.1 ho)
    split_ifs
    · rw [he, add_zero]
    · simp

lemma Q_contr (G : Graph V E) (T S : Finset V) (s0 : V) (hs0 : s0 ∈ S) {x : E → ℝ}
    (hx : x ∈ Q G T) : x ∈ Q (contr G S s0) (contrT T S s0) := by
  refine ⟨⟨fun R hR => ?_, hx.1.2⟩, hx.2⟩
  rw [contr_cut]
  apply hx.1.1
  rw [odd_iff_z2, pre_inter_card_z2 S T R s0 hs0, ← odd_iff_z2]
  exact hR

-- ===== L4 part 2 (session 2): active vertices, cut complement, perturbation, case (b) =====
def charV (F : Finset E) : E → ℝ := fun e => if e ∈ F then 1 else 0

def Act (G : Graph V E) (T : Finset V) : Finset V :=
  Finset.univ.filter (fun v => v ∈ T ∨ ∃ e, v ∈ G.ends e ∧ ¬ (G.ends e).IsDiag)

lemma cut_compl (G : Graph V E) (S : Finset V) : G.cut Sᶜ = G.cut S := by
  ext e
  obtain ⟨⟨a, b⟩, hab⟩ := Quot.exists_rep (G.ends e)
  have h : G.ends e = s(a, b) := hab.symm
  rw [mem_cut_iff G _ e a b h, mem_cut_iff G _ e a b h]
  simp only [Finset.mem_compl]
  tauto

lemma tendsto_aff (a b : ℝ) :
    Filter.Tendsto (fun t : ℝ => a + t * b) (nhdsWithin 0 (Set.Ioi 0)) (nhds a) := by
  have : Filter.Tendsto (fun t : ℝ => a + t * b) (nhds 0) (nhds (a + 0 * b)) :=
    ((continuous_const.add (continuous_id.mul continuous_const)).tendsto 0)
  simpa using this.mono_left nhdsWithin_le_nhds

/-- Perturbation: a direction supported on fractional edges that keeps every tight T-cut tight
must vanish at an extreme point. -/
lemma perturb_zero (G : Graph V E) (T : Finset V) (x : E → ℝ) (hx : x ∈ (Q G T).extremePoints ℝ)
    (d : E → ℝ) (hd : ∀ e, d e ≠ 0 → 0 < x e ∧ x e < 1)
    (hdS : ∀ S : Finset V, Odd (S ∩ T).card → ∑ e ∈ G.cut S, x e = 1 →
      ∑ e ∈ G.cut S, d e = 0) :
    d = 0 := by
  have hxQ : x ∈ Q G T := (mem_extremePoints.1 hx).1
  have hev : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0),
      (∀ e, 0 ≤ x e + t * d e ∧ x e + t * d e ≤ 1 ∧ 0 ≤ x e + t * (-d e) ∧
        x e + t * (-d e) ≤ 1) ∧
      (∀ S : Finset V, Odd (S ∩ T).card →
        1 ≤ ∑ e ∈ G.cut S, x e + t * ∑ e ∈ G.cut S, d e ∧
        1 ≤ ∑ e ∈ G.cut S, x e + t * (-∑ e ∈ G.cut S, d e)) := by
    refine Filter.eventually_and.2
      ⟨Filter.eventually_all.2 fun e => ?_, Filter.eventually_all.2 fun S => ?_⟩
    · by_cases h0 : d e = 0
      · refine Filter.Eventually.of_forall fun t => ?_
        simp only [h0, mul_zero, neg_zero, add_zero]
        exact ⟨hxQ.1.2 e, hxQ.2 e, hxQ.1.2 e, hxQ.2 e⟩
      · obtain ⟨h1, h2⟩ := hd e h0
        have A := tendsto_aff (x e) (d e)
        have B := tendsto_aff (x e) (-d e)
        filter_upwards [A.eventually (lt_mem_nhds h1), A.eventually (gt_mem_nhds h2),
          B.eventually (lt_mem_nhds h1), B.eventually (gt_mem_nhds h2)] with t a1 a2 b1 b2
        exact ⟨a1.le, a2.le, b1.le, b2.le⟩
    · by_cases hS : Odd (S ∩ T).card
      · by_cases ht : ∑ e ∈ G.cut S, x e = 1
        · refine Filter.Eventually.of_forall fun t _ => ?_
          rw [ht, hdS S hS ht]; simp
        · have hlt : 1 < ∑ e ∈ G.cut S, x e := lt_of_le_of_ne (hxQ.1.1 S hS) (Ne.symm ht)
          have A := tendsto_aff (∑ e ∈ G.cut S, x e) (∑ e ∈ G.cut S, d e)
          have B := tendsto_aff (∑ e ∈ G.cut S, x e) (-∑ e ∈ G.cut S, d e)
          filter_upwards [A.eventually (lt_mem_nhds hlt), B.eventually (lt_mem_nhds hlt)]
            with t a b
          exact fun _ => ⟨a.le, b.le⟩
      · exact Filter.Eventually.of_forall fun t h => absurd h hS
  obtain ⟨t, ⟨hA, hB⟩, ht0⟩ := (hev.and self_mem_nhdsWithin).exists
  have ht0' : (0:ℝ) < t := ht0
  have hp : (fun e => x e + t * d e) ∈ Q G T := by
    refine ⟨⟨fun S hS => ?_, fun e => (hA e).1⟩, fun e => (hA e).2.1⟩
    have := (hB S hS).1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]; exact this
  have hm : (fun e => x e + t * (-d e)) ∈ Q G T := by
    refine ⟨⟨fun S hS => ?_, fun e => (hA e).2.2.1⟩, fun e => (hA e).2.2.2⟩
    have := (hB S hS).2
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_neg_distrib]; exact this
  have hseg : x ∈ openSegment ℝ (fun e => x e + t * d e) (fun e => x e + t * (-d e)) := by
    refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
    funext e; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hh := ((mem_extremePoints.1 hx).2 _ hp _ hm hseg).1
  funext e
  have h : x e + t * d e = x e := congrFun hh e
  have h2 : t * d e = 0 := by linarith
  simpa [ht0'.ne'] using h2

lemma act_contr_subset (G : Graph V E) (T S : Finset V) (s0 : V) :
    Act (contr G S s0) (contrT T S s0) ⊆ (Act G T \ S) ∪ {s0} := by
  intro v hv
  by_cases hvs : v = s0
  · simp [hvs]
  rw [Finset.mem_union, Finset.mem_sdiff]; left
  unfold Act at hv ⊢
  rw [Finset.mem_filter_univ] at hv ⊢
  rcases hv with hv | ⟨e, hve, hnd⟩
  · simp only [contrT, Finset.mem_union, Finset.mem_sdiff] at hv
    rcases hv with hv | hv
    · exact ⟨Or.inl hv.1, hv.2⟩
    · split_ifs at hv <;> simp_all
  · obtain ⟨⟨a, b⟩, hab⟩ := Quot.exists_rep (G.ends e)
    have h : G.ends e = s(a, b) := hab.symm
    have h1 : (contr G S s0).ends e = s(collapse S s0 a, collapse S s0 b) := by
      simp [contr, h]
    rw [h1, Sym2.mem_iff] at hve
    rw [h1, Sym2.mk_isDiag_iff] at hnd
    have key : ∀ y, v = collapse S s0 y → y = v ∧ y ∉ S := by
      intro y hy
      unfold collapse at hy
      split_ifs at hy with hyS
      · exact absurd hy hvs
      · exact ⟨hy.symm, hyS⟩
    refine ⟨Or.inr ⟨e, ?_, ?_⟩, ?_⟩
    · rw [h, Sym2.mem_iff]
      rcases hve with hv | hv
      · exact Or.inl (key a hv).1.symm
      · exact Or.inr (key b hv).1.symm
    · rw [h, Sym2.mk_isDiag_iff]
      intro hab'
      exact hnd (by rw [hab'])
    · rcases hve with hv | hv
      · have := key a hv; rw [← this.1]; exact this.2
      · have := key b hv; rw [← this.1]; exact this.2

lemma act_contr_lt (G : Graph V E) (T S : Finset V) (s0 w : V) (hs0 : s0 ∈ Act G T)
    (hw : w ∈ Act G T) (hwS : w ∈ S) (hne : w ≠ s0) :
    (Act (contr G S s0) (contrT T S s0)).card < (Act G T).card := by
  calc _ ≤ ((Act G T).erase w).card := Finset.card_le_card (fun v hv => by
          have := act_contr_subset G T S s0 hv
          rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton] at this
          rw [Finset.mem_erase]
          rcases this with ⟨h1, h2⟩ | h
          · exact ⟨fun h => h2 (h ▸ hwS), h1⟩
          · exact ⟨h ▸ hne.symm, h ▸ hs0⟩)
    _ < _ := Finset.card_erase_lt_of_mem hw

lemma seg_one (p q y z : ℝ) (hp : 0 < p) (hq : 0 < q) (hpq : p + q = 1) (hy : y ≤ 1)
    (hz : z ≤ 1) (h : p * y + q * z = 1) : y = 1 := by
  have h3 : p * (1 - y) = 0 := by
    nlinarith [mul_nonneg hp.le (sub_nonneg.2 hy), mul_nonneg hq.le (sub_nonneg.2 hz)]
  rcases mul_eq_zero.1 h3 with h4 | h4
  · linarith
  · linarith

/-- Case (b): an edge with value 1 can be contracted, keeping x extreme. -/
lemma extreme_contr_edge (G : Graph V E) (T : Finset V) (x : E → ℝ)
    (hx : x ∈ (Q G T).extremePoints ℝ) (e : E) (a b : V) (hab : G.ends e = s(a, b))
    (h1 : x e = 1) :
    x ∈ (Q (contr G {a, b} a) (contrT T {a, b} a)).extremePoints ℝ := by
  have hs0 : a ∈ ({a, b} : Finset V) := by simp
  have key : ∀ w ∈ Q (contr G {a, b} a) (contrT T {a, b} a), w e = 1 → w ∈ Q G T := by
    intro w hw hwe
    refine ⟨⟨fun R hR => ?_, hw.1.2⟩, hw.2⟩
    by_cases heR : e ∈ G.cut R
    · calc (1:ℝ) = w e := hwe.symm
        _ ≤ ∑ g ∈ G.cut R, w g := Finset.single_le_sum (fun g _ => hw.1.2 g) heR
    · have hpre : pre {a, b} a R = R := by
        rw [mem_cut_iff G R e a b hab] at heR
        ext v; rw [mem_pre]
        by_cases hv : v ∈ ({a, b} : Finset V)
        · rw [if_pos hv]
          simp only [Finset.mem_insert, Finset.mem_singleton] at hv
          rcases hv with rfl | rfl <;> tauto
        · rw [if_neg hv]
      have := hw.1.1 R (by
        rw [odd_iff_z2, ← pre_inter_card_z2 _ T R a hs0, hpre, ← odd_iff_z2]; exact hR)
      rwa [contr_cut, hpre] at this
  refine mem_extremePoints.2 ⟨Q_contr G T _ a hs0 (mem_extremePoints.1 hx).1,
    fun y hy z hz hseg => ?_⟩
  obtain ⟨p, q, hp, hq, hpq, hxe⟩ := hseg
  have he := congrFun hxe e
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h1] at he
  have hye : y e = 1 := seg_one p q (y e) (z e) hp hq hpq (hy.2 e) (hz.2 e) he
  have hze : z e = 1 := seg_one q p (z e) (y e) hq hp (by linarith) (hz.2 e) (hy.2 e)
    (by linarith)
  exact (mem_extremePoints.1 hx).2 y (key y hy hye) z (key z hz hze) ⟨p, q, hp, hq, hpq, hxe⟩

-- ===== L4 part 3 (session 2): hull representation and gluing (case c) =====
def A01 (G : Graph V E) (T : Finset V) : Set (E → ℝ) :=
  {y | y ∈ Q G T ∧ ∃ F : Finset E, y = charV F}

lemma charV_nonneg (F : Finset E) (e : E) : 0 ≤ charV F e := by
  unfold charV; split_ifs <;> norm_num

lemma sum_charV (F K : Finset E) : ∑ e ∈ K, charV F e = ((F ∩ K).card : ℝ) := by
  unfold charV
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_comm]

lemma charV_inj {F F' : Finset E} (h : charV F = charV F') : F = F' := by
  ext e
  have := congrFun h e
  unfold charV at this
  by_cases h1 : e ∈ F <;> by_cases h2 : e ∈ F' <;> simp_all

lemma A01_finite (G : Graph V E) (T : Finset V) : (A01 G T).Finite :=
  (Set.finite_range (charV (E := E))).subset (fun y hy => by
    obtain ⟨F, rfl⟩ := hy.2; exact ⟨F, rfl⟩)

lemma Q_sub_hull (G : Graph V E) (T : Finset V)
    (hint : ∀ y ∈ (Q G T).extremePoints ℝ, ∃ F : Finset E, y = charV F) :
    Q G T ⊆ convexHull ℝ (A01 G T) := by
  have hsub : (Q G T).extremePoints ℝ ⊆ A01 G T := fun y hy =>
    ⟨(mem_extremePoints.1 hy).1, hint y hy⟩
  have hcl : IsClosed (convexHull ℝ (A01 G T)) :=
    ((A01_finite G T).isCompact_convexHull ℝ).isClosed
  rw [← closure_convexHull_extremePoints (Q_isCompact G T) (Q_convex G T)]
  exact closure_minimal (convexHull_mono hsub) hcl

lemma hull_rep (G : Graph V E) (T : Finset V) (x : E → ℝ) (hx : x ∈ convexHull ℝ (A01 G T)) :
    ∃ lam : Finset E → ℝ, (∀ F, 0 ≤ lam F) ∧ (∀ F, lam F ≠ 0 → charV F ∈ Q G T) ∧
      ∑ F, lam F = 1 ∧ ∀ g, x g = ∑ F, lam F * charV F g := by
  classical
  set 𝓕 : Finset (Finset E) := Finset.univ.filter (fun F => charV F ∈ Q G T) with h𝓕
  have hA : A01 G T = ↑(𝓕.image charV) := by
    ext y
    simp only [A01, Set.mem_setOf_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe, h𝓕,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hy, F, rfl⟩; exact ⟨F, hy, rfl⟩
    · rintro ⟨F, hF, rfl⟩; exact ⟨hF, F, rfl⟩
  rw [hA, Finset.mem_convexHull'] at hx
  obtain ⟨w, hw0, hw1, hwx⟩ := hx
  rw [Finset.sum_image (fun F _ F' _ h => charV_inj h)] at hw1 hwx
  refine ⟨fun F => if F ∈ 𝓕 then w (charV F) else 0, fun F => ?_, fun F hF => ?_, ?_,
    fun g => ?_⟩
  · dsimp only
    split_ifs with h
    · exact hw0 _ (Finset.mem_image_of_mem _ h)
    · exact le_rfl
  · dsimp only at hF
    split_ifs at hF with h
    · exact (Finset.mem_filter.1 h).2
    · exact absurd rfl hF
  · rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]; exact hw1
  · rw [← hwx, Finset.sum_apply]
    simp only [ite_mul, zero_mul, Pi.smul_apply, smul_eq_mul]
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

lemma mem_hull_of_sum {ι : Type*} [Fintype ι] (C : Set (E → ℝ)) (w : ι → ℝ) (z : ι → E → ℝ)
    (h0 : ∀ i, 0 ≤ w i) (h1 : ∑ i, w i = 1) (hz : ∀ i, w i ≠ 0 → z i ∈ convexHull ℝ C) :
    ∑ i, w i • z i ∈ convexHull ℝ C := by
  classical
  have e1 : ∑ i ∈ Finset.univ.filter (fun i => w i ≠ 0), w i • z i = ∑ i, w i • z i :=
    Finset.sum_filter_of_ne (fun i _ h => fun h0 => h (by rw [h0, zero_smul]))
  have e2 : ∑ i ∈ Finset.univ.filter (fun i => w i ≠ 0), w i = ∑ i, w i :=
    Finset.sum_filter_of_ne (fun i _ h => h)
  rw [← e1]
  exact (convex_convexHull ℝ C).sum_mem (fun i _ => h0 i) (by rw [e2, h1])
    (fun i hi => hz i (Finset.mem_filter.1 hi).2)

lemma lam_le_x (x : E → ℝ) (lam : Finset E → ℝ) (h0 : ∀ F, 0 ≤ lam F)
    (hx : ∀ g, x g = ∑ F, lam F * charV F g) (F : Finset E) (e : E) (he : e ∈ F) :
    lam F ≤ x e := by
  rw [hx]
  have : lam F = lam F * charV F e := by simp [charV, he]
  rw [this]
  exact Finset.single_le_sum (f := fun F' => lam F' * charV F' e)
    (fun F' _ => mul_nonneg (h0 F') (charV_nonneg F' e)) (Finset.mem_univ F)

lemma side_card_one (G' : Graph V E) (T' : Finset V) (x : E → ℝ) (K : Finset E)
    (lam : Finset E → ℝ) (h0 : ∀ F, 0 ≤ lam F) (hQ : ∀ F, lam F ≠ 0 → charV F ∈ Q G' T')
    (h1 : ∑ F, lam F = 1) (hx : ∀ g, x g = ∑ F, lam F * charV F g)
    (hK : ∀ F, charV F ∈ Q G' T' → 1 ≤ (F ∩ K).card) (hxK : ∑ e ∈ K, x e = 1) :
    ∀ F, lam F ≠ 0 → (F ∩ K).card = 1 := by
  have hm : ∑ F, lam F * ((F ∩ K).card : ℝ) = 1 := by
    rw [← hxK]
    simp_rw [hx, ← sum_charV, Finset.mul_sum]
    exact Finset.sum_comm
  have hsum : ∑ F, lam F * (((F ∩ K).card : ℝ) - 1) = 0 := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hm, h1, sub_self]
  have hnn : ∀ F ∈ Finset.univ, 0 ≤ lam F * (((F ∩ K).card : ℝ) - 1) := by
    intro F _
    by_cases hF : lam F = 0
    · simp [hF]
    · have := hK F (hQ F hF)
      exact mul_nonneg (h0 F) (sub_nonneg.2 (by exact_mod_cast this))
  intro F hF
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum F (Finset.mem_univ _)
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h hF
  · have : ((F ∩ K).card : ℝ) = 1 := by linarith
    exact_mod_cast this

lemma side_vec (G' : Graph V E) (T' : Finset V) (x : E → ℝ) (K : Finset E)
    (lam : Finset E → ℝ) (h0 : ∀ F, 0 ≤ lam F) (hQ : ∀ F, lam F ≠ 0 → charV F ∈ Q G' T')
    (hx : ∀ g, x g = ∑ F, lam F * charV F g)
    (hone : ∀ F, lam F ≠ 0 → (F ∩ K).card = 1) :
    (∀ e ∈ K, 0 < x e → (fun g => (∑ F, lam F * charV F e * charV F g) / x e) ∈
        convexHull ℝ {y | ∃ F, y = charV F ∧ charV F ∈ Q G' T' ∧ F ∩ K = {e}}) ∧
    (∀ g, ∑ e ∈ K.filter (fun e => 0 < x e),
        x e * ((∑ F, lam F * charV F e * charV F g) / x e) = x g) := by
  refine ⟨fun e heK hxe => ?_, fun g => ?_⟩
  · have hw : (fun g => (∑ F, lam F * charV F e * charV F g) / x e) =
        ∑ F, (lam F * charV F e / x e) • charV F := by
      funext g
      rw [Finset.sum_apply, Finset.sum_div]
      refine Finset.sum_congr rfl fun F _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [hw]
    refine mem_hull_of_sum _ (fun F => lam F * charV F e / x e) charV
      (fun F => div_nonneg (mul_nonneg (h0 F) (charV_nonneg F e)) hxe.le) ?_ ?_
    · rw [← Finset.sum_div, div_eq_one_iff_eq hxe.ne']; exact (hx e).symm
    · intro F hF
      have hl : lam F ≠ 0 := by intro h; apply hF; simp [h]
      have he : e ∈ F := by
        by_contra h; apply hF; simp [charV, h]
      refine subset_convexHull ℝ _ ⟨F, rfl, hQ F hl, ?_⟩
      obtain ⟨a, ha⟩ := Finset.card_eq_one.1 (hone F hl)
      have : e ∈ F ∩ K := Finset.mem_inter.2 ⟨he, heK⟩
      rw [ha, Finset.mem_singleton] at this
      rw [ha, this]
  · have step : ∀ e ∈ K.filter (fun e => 0 < x e),
        x e * ((∑ F, lam F * charV F e * charV F g) / x e) =
          ∑ F, lam F * charV F e * charV F g := by
      intro e he
      have hne : x e ≠ 0 := (Finset.mem_filter.1 he).2.ne'
      field_simp
    rw [Finset.sum_congr rfl step, Finset.sum_comm, hx g]
    refine Finset.sum_congr rfl fun F _ => ?_
    by_cases hl : lam F = 0
    · simp [hl]
    · obtain ⟨a, ha⟩ := Finset.card_eq_one.1 (hone F hl)
      have haF : a ∈ F ∧ a ∈ K := Finset.mem_inter.1 (ha ▸ Finset.mem_singleton_self a)
      have hxa : 0 < x a := lt_of_lt_of_le (lt_of_le_of_ne (h0 F) (Ne.symm hl))
        (lam_le_x x lam h0 hx F a haF.1)
      rw [Finset.sum_eq_single a]
      · simp [charV, haF.1]
      · intro b hb hba
        have hbF : b ∉ F := fun hbF => hba (by
          have : b ∈ F ∩ K := Finset.mem_inter.2 ⟨hbF, (Finset.mem_filter.1 hb).1⟩
          rwa [ha, Finset.mem_singleton] at this)
        simp [charV, hbF]
      · intro ha'; exact absurd (Finset.mem_filter.2 ⟨haF.2, hxa⟩) ha'

def inS (G : Graph V E) (S : Finset V) : Finset E :=
  Finset.univ.filter (fun g => ∀ v ∈ G.ends g, v ∈ S)

def glueV (G : Graph V E) (S : Finset V) (y w : E → ℝ) : E → ℝ :=
  fun g => if g ∈ inS G S then w g else y g

def glueF (G : Graph V E) (S : Finset V) (F F' : Finset E) : Finset E :=
  F.filter (· ∉ inS G S) ∪ F'.filter (· ∈ inS G S)

lemma inS_iff (G : Graph V E) (S : Finset V) {g : E} {a b : V} (h : G.ends g = s(a, b)) :
    g ∈ inS G S ↔ a ∈ S ∧ b ∈ S := by
  simp [inS, h, Sym2.mem_iff, or_imp, forall_and]

lemma glueV_charV (G : Graph V E) (S : Finset V) (F F' : Finset E) :
    glueV G S (charV F) (charV F') = charV (glueF G S F F') := by
  funext g
  by_cases hg : g ∈ inS G S <;> simp [glueV, charV, glueF, hg]

lemma glue_hull (G : Graph V E) (S : Finset V) (C X Y : Set (E → ℝ))
    (h : ∀ y ∈ X, ∀ w ∈ Y, glueV G S y w ∈ convexHull ℝ C) :
    ∀ y ∈ convexHull ℝ X, ∀ w ∈ convexHull ℝ Y, glueV G S y w ∈ convexHull ℝ C := by
  have step1 : ∀ w ∈ Y, ∀ y ∈ convexHull ℝ X, glueV G S y w ∈ convexHull ℝ C := by
    intro w hw
    have hconv : Convex ℝ {y | glueV G S y w ∈ convexHull ℝ C} := by
      intro y1 h1 y2 h2 a b ha hb hab
      have e : glueV G S (a • y1 + b • y2) w = a • glueV G S y1 w + b • glueV G S y2 w := by
        funext g
        simp only [glueV, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        split_ifs
        · linear_combination (-(w g)) * hab
        · ring
      rw [Set.mem_setOf_eq, e]; exact convex_convexHull ℝ C h1 h2 ha hb hab
    exact convexHull_min (fun y hy => h y hy w hw) hconv
  intro y hy
  have hconv : Convex ℝ {w | glueV G S y w ∈ convexHull ℝ C} := by
    intro w1 h1 w2 h2 a b ha hb hab
    have e : glueV G S y (a • w1 + b • w2) = a • glueV G S y w1 + b • glueV G S y w2 := by
      funext g
      simp only [glueV, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      split_ifs
      · ring
      · linear_combination (-(y g)) * hab
    rw [Set.mem_setOf_eq, e]; exact convex_convexHull ℝ C h1 h2 ha hb hab
  exact convexHull_min (fun w hw => step1 w hw y hy) hconv

lemma covers_of_Q (G : Graph V E) (T : Finset V) (F : Finset E) (hF : charV F ∈ Q G T) :
    Covers G T F := by
  intro R hR
  have h := hF.1.1 R hR
  rw [sum_charV] at h
  rw [← Finset.card_pos]
  exact_mod_cast (show (0:ℝ) < ((F ∩ G.cut R).card : ℝ) by linarith)

lemma Q_of_join_sub (G : Graph V E) (T : Finset V) (J H : Finset E) (hJ : G.IsTJoin T J)
    (hJH : J ⊆ H) : charV H ∈ Q G T := by
  refine ⟨⟨fun R hR => ?_, fun e => charV_nonneg H e⟩, fun e => ?_⟩
  · rw [sum_charV]
    have h := isTJoin_cut G T J hJ R
    rw [(odd_iff_z2 _).1 hR] at h
    have hpos : 0 < (J ∩ G.cut R).card := by
      rcases Nat.eq_zero_or_pos (J ∩ G.cut R).card with h0 | h0
      · rw [h0] at h; simp at h
      · exact h0
    have : (J ∩ G.cut R).card ≤ (H ∩ G.cut R).card :=
      Finset.card_le_card (Finset.inter_subset_inter hJH (subset_refl _))
    exact_mod_cast (show 1 ≤ (H ∩ G.cut R).card by omega)
  · unfold charV; split_ifs <;> norm_num

lemma join_hits (G' : Graph V E) (T' : Finset V) (J F : Finset E) (u : V) (e : E)
    (hJ : G'.IsTJoin T' J) (hJF : J ⊆ F) (hu : u ∈ T') (hFe : F ∩ G'.cut {u} = {e}) :
    e ∈ J := by
  have h := isTJoin_cut G' T' J hJ {u}
  rw [Finset.singleton_inter_of_mem hu] at h
  simp only [Finset.card_singleton, Nat.cast_one] at h
  have hne : (J ∩ G'.cut {u}).Nonempty := by
    rw [← Finset.card_pos]
    rcases Nat.eq_zero_or_pos (J ∩ G'.cut {u}).card with h0 | h0
    · rw [h0] at h; simp at h
    · exact h0
  obtain ⟨g, hg⟩ := hne
  have : g ∈ F ∩ G'.cut {u} :=
    Finset.mem_inter.2 ⟨hJF (Finset.mem_inter.1 hg).1, (Finset.mem_inter.1 hg).2⟩
  rw [hFe, Finset.mem_singleton] at this
  exact this ▸ (Finset.mem_inter.1 hg).1

lemma pre_self (S : Finset V) (s0 : V) (hs0 : s0 ∈ S) : pre S s0 {s0} = S := by
  ext v; rw [mem_pre]
  by_cases hv : v ∈ S
  · simp [hv]
  · rw [if_neg hv, Finset.mem_singleton]
    exact ⟨fun h => (hv (h ▸ hs0)).elim, fun h => (hv h).elim⟩

lemma pre_single (S : Finset V) (s0 v : V) (hs0 : s0 ∈ S) (hv : v ∉ S) :
    pre S s0 {v} = {v} := by
  ext w; rw [mem_pre, Finset.mem_singleton]
  by_cases hw : w ∈ S
  · rw [if_pos hw, Finset.mem_singleton]
    exact ⟨fun h => (hv (h ▸ hs0)).elim, fun h => (hv (h ▸ hw)).elim⟩
  · rw [if_neg hw, Finset.mem_singleton]

/-- Gluing two contracted 0/1 covers that cross the tight cut at the same edge. -/
lemma glue_mem (G : Graph V E) (T S : Finset V) (s0 t0 : V) (hs0 : s0 ∈ S) (ht0 : t0 ∉ S)
    (hST : Odd (S ∩ T).card) (hScT : Odd (Sᶜ ∩ T).card) (e : E) (F F' : Finset E)
    (hF : charV F ∈ Q (contr G S s0) (contrT T S s0)) (hFe : F ∩ G.cut S = {e})
    (hF' : charV F' ∈ Q (contr G Sᶜ t0) (contrT T Sᶜ t0)) (hF'e : F' ∩ G.cut S = {e}) :
    charV (glueF G S F F') ∈ Q G T := by
  have ht0' : t0 ∈ Sᶜ := Finset.mem_compl.2 ht0
  obtain ⟨J1, hJ1F, hJ1⟩ := covers_exists_tjoin _ F _ (covers_of_Q _ _ _ hF)
  obtain ⟨J2, hJ2F, hJ2⟩ := covers_exists_tjoin _ F' _ (covers_of_Q _ _ _ hF')
  have hcut1 : (contr G S s0).cut {s0} = G.cut S := by rw [contr_cut, pre_self S s0 hs0]
  have hcut2 : (contr G Sᶜ t0).cut {t0} = G.cut S := by
    rw [contr_cut, pre_self Sᶜ t0 ht0', cut_compl]
  have he1 : e ∈ J1 := join_hits _ _ J1 F s0 e hJ1 hJ1F (by simp [contrT, hST])
    (by rw [hcut1]; exact hFe)
  have he2 : e ∈ J2 := join_hits _ _ J2 F' t0 e hJ2 hJ2F (by simp [contrT, hScT])
    (by rw [hcut2]; exact hF'e)
  have hJ1S : ∀ g ∈ J1, g ∈ G.cut S → g = e := fun g hg hgS => by
    have : g ∈ F ∩ G.cut S := Finset.mem_inter.2 ⟨hJ1F hg, hgS⟩
    rwa [hFe, Finset.mem_singleton] at this
  have hJ2S : ∀ g ∈ J2, g ∈ G.cut S → g = e := fun g hg hgS => by
    have : g ∈ F' ∩ G.cut S := Finset.mem_inter.2 ⟨hJ2F hg, hgS⟩
    rwa [hF'e, Finset.mem_singleton] at this
  have hsub : glueF G S J1 J2 ⊆ glueF G S F F' := by
    intro g hg
    simp only [glueF, Finset.mem_union, Finset.mem_filter] at hg ⊢
    rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨hJ1F h1, h2⟩
    · exact Or.inr ⟨hJ2F h1, h2⟩
  refine Q_of_join_sub G T _ _ (fun v => ?_) hsub
  by_cases hv : v ∈ S
  · have e1 : glueF G S J1 J2 ∩ G.cut {v} = J2 ∩ (contr G Sᶜ t0).cut {v} := by
      rw [contr_cut, pre_single Sᶜ t0 v ht0' (by simpa using hv)]
      ext g
      obtain ⟨⟨a, b⟩, hab⟩ := Quot.exists_rep (G.ends g)
      have h : G.ends g = s(a, b) := hab.symm
      have hc := mem_cut_iff G S g a b h
      simp only [Finset.mem_inter, glueF, Finset.mem_union, Finset.mem_filter,
        mem_cut_iff G {v} g a b h, inS_iff G S h, Finset.mem_singleton]
      constructor
      · rintro ⟨hJ, hcv⟩
        refine ⟨?_, hcv⟩
        rcases hJ with ⟨hg1, hn⟩ | ⟨hg2, _⟩
        · have hgS : g ∈ G.cut S := by
            rw [hc]; rcases hcv with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> tauto
          rw [hJ1S g hg1 hgS]; exact he2
        · exact hg2
      · rintro ⟨hg2, hcv⟩
        refine ⟨?_, hcv⟩
        by_cases hin : a ∈ S ∧ b ∈ S
        · exact Or.inr ⟨hg2, hin⟩
        · left
          have hgS : g ∈ G.cut S := by
            rw [hc]; rcases hcv with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> tauto
          rw [hJ2S g hg2 hgS]; exact ⟨he1, hin⟩
    have e2 : T ∩ {v} = contrT T Sᶜ t0 ∩ {v} := by
      ext w
      simp only [contrT, if_pos hScT, Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff,
        Finset.mem_singleton, Finset.mem_compl, not_not]
      constructor
      · rintro ⟨h1, rfl⟩; exact ⟨Or.inl ⟨h1, hv⟩, rfl⟩
      · rintro ⟨h1 | h1, rfl⟩
        · exact ⟨h1.1, rfl⟩
        · exact absurd (h1 ▸ hv) ht0
    rw [e1, e2]; exact hJ2 v
  · have e1 : glueF G S J1 J2 ∩ G.cut {v} = J1 ∩ (contr G S s0).cut {v} := by
      rw [contr_cut, pre_single S s0 v hs0 hv]
      ext g
      obtain ⟨⟨a, b⟩, hab⟩ := Quot.exists_rep (G.ends g)
      have h : G.ends g = s(a, b) := hab.symm
      simp only [Finset.mem_inter, glueF, Finset.mem_union, Finset.mem_filter,
        mem_cut_iff G {v} g a b h, inS_iff G S h, Finset.mem_singleton]
      constructor
      · rintro ⟨hJ, hcv⟩
        refine ⟨?_, hcv⟩
        rcases hJ with ⟨hg1, _⟩ | ⟨_, hin⟩
        · exact hg1
        · exfalso; rcases hcv with ⟨rfl, _⟩ | ⟨rfl, _⟩
          · exact hv hin.1
          · exact hv hin.2
      · rintro ⟨hg1, hcv⟩
        refine ⟨Or.inl ⟨hg1, fun hin => ?_⟩, hcv⟩
        rcases hcv with ⟨rfl, _⟩ | ⟨rfl, _⟩
        · exact hv hin.1
        · exact hv hin.2
    have e2 : T ∩ {v} = contrT T S s0 ∩ {v} := by
      ext w
      simp only [contrT, if_pos hST, Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff,
        Finset.mem_singleton]
      constructor
      · rintro ⟨h1, rfl⟩; exact ⟨Or.inl ⟨h1, hv⟩, rfl⟩
      · rintro ⟨h1 | h1, rfl⟩
        · exact ⟨h1.1, rfl⟩
        · exact absurd (h1 ▸ hs0) hv
    rw [e1, e2]; exact hJ1 v

-- ===== L4 part 4 (session 2): case (c) assembly and case (d) infrastructure =====
lemma odd_compl_inter (S T : Finset V) (hT : Even T.card) (hST : Odd (S ∩ T).card) :
    Odd (Sᶜ ∩ T).card := by
  have hsplit : (S ∩ T).card + (Sᶜ ∩ T).card = T.card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext v; by_cases hv : v ∈ S <;> simp [hv]
    · rw [Finset.disjoint_left]; intro v h1 h2
      exact (Finset.mem_compl.1 (Finset.mem_inter.1 h2).1) (Finset.mem_inter.1 h1).1
  have h : Even ((S ∩ T).card + (Sᶜ ∩ T).card) := hsplit ▸ hT
  exact Nat.not_even_iff_odd.1 (fun hb => (Nat.not_even_iff_odd.2 hST) ((Nat.even_add.1 h).2 hb))

lemma ext_mem_of_hull (G : Graph V E) (T : Finset V) (x : E → ℝ)
    (hx : x ∈ (Q G T).extremePoints ℝ) (hh : x ∈ convexHull ℝ (A01 G T)) :
    ∃ F : Finset E, x = charV F := by
  have hsub : convexHull ℝ (A01 G T) ⊆ Q G T := convexHull_min (fun y hy => hy.1) (Q_convex G T)
  have := inter_extremePoints_subset_extremePoints_of_subset hsub ⟨hh, hx⟩
  exact (extremePoints_convexHull_subset this).2

/-- Case (c): a tight T-cut; both shrunken sides are integral, glue. -/
lemma case_c (G : Graph V E) (T : Finset V) (hT : Even T.card) (x : E → ℝ)
    (hx : x ∈ (Q G T).extremePoints ℝ) (S : Finset V) (s0 t0 : V) (hs0 : s0 ∈ S) (ht0 : t0 ∉ S)
    (hST : Odd (S ∩ T).card) (htight : ∑ e ∈ G.cut S, x e = 1)
    (h1 : ∀ y ∈ (Q (contr G S s0) (contrT T S s0)).extremePoints ℝ, ∃ F : Finset E, y = charV F)
    (h2 : ∀ y ∈ (Q (contr G Sᶜ t0) (contrT T Sᶜ t0)).extremePoints ℝ,
      ∃ F : Finset E, y = charV F) :
    ∃ F : Finset E, x = charV F := by
  have hScT : Odd (Sᶜ ∩ T).card := odd_compl_inter S T hT hST
  have ht0' : t0 ∈ Sᶜ := Finset.mem_compl.2 ht0
  have hxQ := (mem_extremePoints.1 hx).1
  obtain ⟨lam, l0, lQ, l1, lx⟩ := hull_rep _ _ x (Q_sub_hull _ _ h1 (Q_contr G T S s0 hs0 hxQ))
  obtain ⟨mu, m0, mQ, m1, mx⟩ :=
    hull_rep _ _ x (Q_sub_hull _ _ h2 (Q_contr G T Sᶜ t0 ht0' hxQ))
  have hK1 : ∀ F, charV F ∈ Q (contr G S s0) (contrT T S s0) → 1 ≤ (F ∩ G.cut S).card := by
    intro F hF
    have := hF.1.1 {s0} (by rw [Finset.singleton_inter_of_mem (by simp [contrT, hST])]; simp)
    rw [contr_cut, pre_self S s0 hs0, sum_charV] at this
    exact_mod_cast this
  have hK2 : ∀ F, charV F ∈ Q (contr G Sᶜ t0) (contrT T Sᶜ t0) → 1 ≤ (F ∩ G.cut S).card := by
    intro F hF
    have := hF.1.1 {t0} (by rw [Finset.singleton_inter_of_mem (by simp [contrT, hScT])]; simp)
    rw [contr_cut, pre_self Sᶜ t0 ht0', cut_compl, sum_charV] at this
    exact_mod_cast this
  have lone := side_card_one _ _ x _ lam l0 lQ l1 lx hK1 htight
  have mone := side_card_one _ _ x _ mu m0 mQ m1 mx hK2 htight
  obtain ⟨u1, u2⟩ := side_vec _ _ x _ lam l0 lQ lx lone
  obtain ⟨v1, v2⟩ := side_vec _ _ x _ mu m0 mQ mx mone
  apply ext_mem_of_hull G T x hx
  have hrep : x = ∑ e, (if e ∈ (G.cut S).filter (fun e => 0 < x e) then x e else 0) •
      glueV G S (fun g => (∑ F, lam F * charV F e * charV F g) / x e)
        (fun g => (∑ F, mu F * charV F e * charV F g) / x e) := by
    funext g
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, ite_mul, zero_mul]
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    by_cases hg : g ∈ inS G S
    · simp only [glueV, hg, if_true]; exact (v2 g).symm
    · simp only [glueV, hg, if_false]; exact (u2 g).symm
  rw [hrep]
  refine mem_hull_of_sum _ _ _ (fun e => ?_) ?_ (fun e he => ?_)
  · split_ifs with h
    · exact (Finset.mem_filter.1 h).2.le
    · exact le_rfl
  · rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, ← htight]
    exact Finset.sum_filter_of_ne (fun e _ h => lt_of_le_of_ne (hxQ.1.2 e) (Ne.symm h))
  · have heD : e ∈ (G.cut S).filter (fun e => 0 < x e) := by
      by_contra h; exact he (if_neg h)
    obtain ⟨heS, hxe⟩ := Finset.mem_filter.1 heD
    exact glue_hull G S (A01 G T) _ _ (fun y hy w hw => by
      obtain ⟨F, rfl, hF, hFe⟩ := hy
      obtain ⟨F', rfl, hF', hF'e⟩ := hw
      rw [glueV_charV]
      exact subset_convexHull ℝ _
        ⟨glue_mem G T S s0 t0 hs0 ht0 hST hScT e F F' hF hFe hF' hF'e, _, rfl⟩)
      _ (u1 e heS hxe) _ (v1 e heS hxe)

lemma act_of_end (G : Graph V E) (T : Finset V) (g : E) (a b : V) (h : G.ends g = s(a, b))
    (hab : a ≠ b) : a ∈ Act G T ∧ b ∈ Act G T := by
  unfold Act
  rw [Finset.mem_filter_univ, Finset.mem_filter_univ]
  refine ⟨Or.inr ⟨g, ?_, ?_⟩, Or.inr ⟨g, ?_, ?_⟩⟩ <;>
    first
    | (rw [h]; exact Sym2.mem_mk_left a b)
    | (rw [h]; exact Sym2.mem_mk_right a b)
    | (rw [h, Sym2.mk_isDiag_iff]; exact hab)

/-- No nontrivial tight T-cut: a tight T-cut is a star. -/
lemma tight_star (G : Graph V E) (T : Finset V) (hT : Even T.card) (S : Finset V)
    (hS : Odd (S ∩ T).card)
    (hsmall : (S ∩ Act G T).card ≤ 1 ∨ (Sᶜ ∩ Act G T).card ≤ 1) :
    ∃ v ∈ T, G.cut S = G.cut {v} := by
  have key : ∀ R : Finset V, Odd (R ∩ T).card → (R ∩ Act G T).card ≤ 1 →
      ∃ v ∈ T, G.cut R = G.cut {v} := by
    intro R hR hc
    obtain ⟨v, hv⟩ := Finset.card_pos.1 hR.pos
    obtain ⟨hvR, hvT⟩ := Finset.mem_inter.1 hv
    have hvA : v ∈ Act G T := by unfold Act; rw [Finset.mem_filter_univ]; exact Or.inl hvT
    have huniq : ∀ y ∈ R, y ∈ Act G T → y = v := fun y hy hyA =>
      Finset.card_le_one.1 hc y (Finset.mem_inter.2 ⟨hy, hyA⟩) v (Finset.mem_inter.2 ⟨hvR, hvA⟩)
    refine ⟨v, hvT, ?_⟩
    ext g
    obtain ⟨⟨a, b⟩, hab⟩ := Quot.exists_rep (G.ends g)
    have h : G.ends g = s(a, b) := hab.symm
    rw [mem_cut_iff G R g a b h, mem_cut_iff G {v} g a b h]
    simp only [Finset.mem_singleton]
    by_cases hab' : a = b
    · subst hab'; tauto
    · obtain ⟨haA, hbA⟩ := act_of_end G T g a b h hab'
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact Or.inl ⟨huniq a h1 haA, fun hb => h2 (hb ▸ hvR)⟩
        · exact Or.inr ⟨huniq b h1 hbA, fun ha => h2 (ha ▸ hvR)⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact Or.inl ⟨h1 ▸ hvR, fun hb => h2 (huniq b hb hbA)⟩
        · exact Or.inr ⟨h1 ▸ hvR, fun ha => h2 (huniq a ha haA)⟩
  rcases hsmall with h | h
  · exact key S hS h
  · obtain ⟨v, hv, hc⟩ := key Sᶜ (odd_compl_inter S T hT hS) h
    exact ⟨v, hv, by rw [← cut_compl, hc]⟩

/-- At an extreme point, loops are integral. -/
lemma loop_int (G : Graph V E) (T : Finset V) (x : E → ℝ) (hx : x ∈ (Q G T).extremePoints ℝ)
    (e : E) (he : (G.ends e).IsDiag) : x e = 0 ∨ x e = 1 := by
  by_contra hc
  push_neg at hc
  have hxQ := (mem_extremePoints.1 hx).1
  have hcut : ∀ S : Finset V, e ∉ G.cut S := by
    intro S
    obtain ⟨⟨a, b⟩, hab⟩ := Quot.exists_rep (G.ends e)
    have h : G.ends e = s(a, b) := hab.symm
    rw [h, Sym2.mk_isDiag_iff] at he
    rw [mem_cut_iff G S e a b h, he]; tauto
  have hd : charV {e} = 0 := perturb_zero G T x hx (charV {e})
    (fun g hg => by
      have hge : g = e := by by_contra h; apply hg; simp [charV, h]
      subst hge
      exact ⟨lt_of_le_of_ne (hxQ.1.2 g) (Ne.symm hc.1), lt_of_le_of_ne (hxQ.2 g) hc.2⟩)
    (fun S _ _ => by rw [sum_charV, Finset.singleton_inter_of_notMem (hcut S)]; simp)
  have := congrFun hd e
  simp [charV] at this

/-- Rank count: at an extreme point with only star-shaped tight T-cuts,
#fractional edges ≤ #tight T-vertices. -/
lemma card_frac_le (G : Graph V E) (T : Finset V) (hT : Even T.card) (x : E → ℝ)
    (hx : x ∈ (Q G T).extremePoints ℝ)
    (hnoc : ∀ S : Finset V, Odd (S ∩ T).card → ∑ e ∈ G.cut S, x e = 1 →
      (S ∩ Act G T).card ≤ 1 ∨ (Sᶜ ∩ Act G T).card ≤ 1) :
    (Finset.univ.filter (fun e => 0 < x e ∧ x e < 1)).card ≤
      (Finset.univ.filter (fun v => v ∈ T ∧ ∑ e ∈ G.cut {v}, x e = 1)).card := by
  classical
  set Ep := Finset.univ.filter (fun e => 0 < x e ∧ x e < 1) with hEp
  set Tt := Finset.univ.filter (fun v => v ∈ T ∧ ∑ e ∈ G.cut {v}, x e = 1) with hTt
  let ext : ({e // e ∈ Ep} → ℝ) → E → ℝ := fun d e => if h : e ∈ Ep then d ⟨e, h⟩ else 0
  let L : ({e // e ∈ Ep} → ℝ) →ₗ[ℝ] ({v // v ∈ Tt} → ℝ) :=
    { toFun := fun d v => ∑ e ∈ G.cut {v.1}, ext d e
      map_add' := fun d1 d2 => by
        funext v
        simp only [Pi.add_apply, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun e _ => ?_
        simp only [ext]; split_ifs <;> simp
      map_smul' := fun c d => by
        funext v
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        simp only [ext]; split_ifs <;> simp }
  by_contra hlt
  push_neg at hlt
  have hker : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]; exact hlt)
  obtain ⟨d, hdk, hd0⟩ := (Submodule.ne_bot_iff _).1 hker
  have hz : ext d = 0 := perturb_zero G T x hx (ext d)
    (fun e he => by
      simp only [ext] at he
      split_ifs at he with h
      · exact (Finset.mem_filter.1 h).2
      · exact absurd rfl he)
    (fun S hS ht => by
      obtain ⟨v, hvT, hcut⟩ := tight_star G T hT S hS (hnoc S hS ht)
      have hvTt : v ∈ Tt := Finset.mem_filter.2 ⟨Finset.mem_univ _, hvT, by rw [← hcut]; exact ht⟩
      have := congrFun (LinearMap.mem_ker.1 hdk) ⟨v, hvTt⟩
      rw [hcut]; exact this)
  apply hd0
  funext ⟨e, he⟩
  have := congrFun hz e
  simpa [ext, he] using this

-- ===== L4 part 5 (session 2): strong induction on #active vertices, case (d) as hypothesis =====
lemma even_contrT (T S : Finset V) (s0 : V) (hs0 : s0 ∈ S) (hT : Even T.card) :
    Even (contrT T S s0).card := by
  have hsplit : (T \ S).card + (S ∩ T).card = T.card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext v; by_cases hv : v ∈ S <;> simp [hv]
    · rw [Finset.disjoint_left]; intro v h1 h2
      exact (Finset.mem_sdiff.1 h1).2 (Finset.mem_inter.1 h2).1
  have h : Even ((T \ S).card + (S ∩ T).card) := hsplit ▸ hT
  unfold contrT
  by_cases ho : Odd (S ∩ T).card
  · rw [if_pos ho, Finset.card_union_of_disjoint (by
      rw [Finset.disjoint_singleton_right]; intro h; exact (Finset.mem_sdiff.1 h).2 hs0),
      Finset.card_singleton]
    have : Odd (T \ S).card := Nat.not_even_iff_odd.1
      (fun he => (Nat.not_even_iff_odd.2 ho) ((Nat.even_add.1 h).1 he))
    exact this.add_one
  · rw [if_neg ho, Finset.union_empty]
    exact (Nat.even_add.1 h).2 (Nat.not_odd_iff_even.1 ho)

theorem L4_of
    (hD : ∀ (G : Graph V E) (T : Finset V), Even T.card → ∀ x ∈ (Q G T).extremePoints ℝ,
      (∀ e, ¬ (G.ends e).IsDiag → x e ≠ 1) →
      (∀ S : Finset V, Odd (S ∩ T).card → ∑ e ∈ G.cut S, x e = 1 →
        (S ∩ Act G T).card ≤ 1 ∨ (Sᶜ ∩ Act G T).card ≤ 1) →
      ∃ F : Finset E, x = charV F) :
    ∀ (n : ℕ) (G : Graph V E) (T : Finset V), (Act G T).card = n → Even T.card →
      ∀ x ∈ (Q G T).extremePoints ℝ, ∃ F : Finset E, x = charV F := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G T hn hT x hx
  by_cases h1 : ∃ e, ¬ (G.ends e).IsDiag ∧ x e = 1
  · obtain ⟨e, hnd, hxe⟩ := h1
    obtain ⟨⟨a, b⟩, hab⟩ := Quot.exists_rep (G.ends e)
    have h : G.ends e = s(a, b) := hab.symm
    have hne : a ≠ b := by rw [h, Sym2.mk_isDiag_iff] at hnd; exact hnd
    obtain ⟨haA, hbA⟩ := act_of_end G T e a b h hne
    have hlt := act_contr_lt G T {a, b} a b haA hbA (by simp) hne.symm
    exact ih _ (lt_of_lt_of_eq hlt hn) _ _ rfl (even_contrT T {a, b} a (by simp) hT) x
      (extreme_contr_edge G T x hx e a b h hxe)
  by_cases h2 : ∃ S : Finset V, Odd (S ∩ T).card ∧ ∑ e ∈ G.cut S, x e = 1 ∧
      1 < (S ∩ Act G T).card ∧ 1 < (Sᶜ ∩ Act G T).card
  · obtain ⟨S, hS, ht, hc1, hc2⟩ := h2
    obtain ⟨s0, hs0, w, hw, hsw⟩ := Finset.one_lt_card.1 hc1
    obtain ⟨t0, ht0, w', hw', htw⟩ := Finset.one_lt_card.1 hc2
    rw [Finset.mem_inter] at hs0 hw ht0 hw'
    have ht0S : t0 ∉ S := Finset.mem_compl.1 ht0.1
    refine case_c G T hT x hx S s0 t0 hs0.1 ht0S hS ht (fun y hy => ?_) (fun y hy => ?_)
    · exact ih _ (lt_of_lt_of_eq (act_contr_lt G T S s0 w hs0.2 hw.2 hw.1 (Ne.symm hsw)) hn)
        _ _ rfl (even_contrT T S s0 hs0.1 hT) y hy
    · exact ih _ (lt_of_lt_of_eq (act_contr_lt G T Sᶜ t0 w' ht0.2 hw'.2 hw'.1 (Ne.symm htw)) hn)
        _ _ rfl (even_contrT T Sᶜ t0 ht0.1 hT) y hy
  · push_neg at h1 h2
    refine hD G T hT x hx (fun e he => h1 e he) (fun S hS ht => ?_)
    by_contra hc
    push_neg at hc
    exact absurd (h2 S hS ht hc.1) (not_le.2 hc.2)

-- ===== L4 part 6 (session 2): case (d) degree counting =====
lemma nonloop_of_cut (G : Graph V E) (S : Finset V) (e : E) (he : e ∈ G.cut S) :
    ¬ (G.ends e).IsDiag := by
  obtain ⟨⟨a, b⟩, hab⟩ := Quot.exists_rep (G.ends e)
  have h : G.ends e = s(a, b) := hab.symm
  rw [mem_cut_iff G S e a b h] at he
  rw [h, Sym2.mk_isDiag_iff]; rintro rfl; tauto

lemma frac_ge_two (G : Graph V E) (T : Finset V) (x : E → ℝ) (hxQ : x ∈ Q G T)
    (hno1 : ∀ e, ¬ (G.ends e).IsDiag → x e ≠ 1) (v : V) (hv : ∑ e ∈ G.cut {v}, x e = 1) :
    2 ≤ ((Finset.univ.filter (fun e => 0 < x e ∧ x e < 1)).filter
      (fun e => e ∈ G.cut {v})).card := by
  by_contra hlt
  have hle : ((Finset.univ.filter (fun e => 0 < x e ∧ x e < 1)).filter
      (fun e => e ∈ G.cut {v})).card ≤ 1 := by omega
  have hnl : ∀ e ∈ G.cut {v}, x e < 1 := fun e he =>
    lt_of_le_of_ne (hxQ.2 e) (hno1 e (nonloop_of_cut G {v} e he))
  have hs : ∑ e ∈ ((Finset.univ.filter (fun e => 0 < x e ∧ x e < 1)).filter
      (fun e => e ∈ G.cut {v})), x e = 1 := by
    refine (Finset.sum_subset (fun e he => (Finset.mem_filter.1 he).2) (fun e he hn => ?_)).trans hv
    have hnot : ¬ (0 < x e ∧ x e < 1) := fun h =>
      hn (Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩, he⟩)
    by_contra hne
    exact hnot ⟨lt_of_le_of_ne (hxQ.1.2 e) (Ne.symm hne), hnl e he⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hle with h0 | h1
  · rw [Finset.card_eq_zero.1 h0, Finset.sum_empty] at hs; norm_num at hs
  · obtain ⟨e, he⟩ := Finset.card_eq_one.1 h1
    have hmem : e ∈ G.cut {v} := by
      have : e ∈ ((Finset.univ.filter (fun e => 0 < x e ∧ x e < 1)).filter
          (fun e => e ∈ G.cut {v})) := by rw [he]; simp
      exact (Finset.mem_filter.1 this).2
    rw [he, Finset.sum_singleton] at hs
    linarith [hnl e hmem]

/-- Double counting: every tight T-vertex has exactly two fractional edges, and both ends of
every fractional edge are tight T-vertices. -/
lemma deg_two (G : Graph V E) (T : Finset V) (hT : Even T.card) (x : E → ℝ)
    (hx : x ∈ (Q G T).extremePoints ℝ) (hno1 : ∀ e, ¬ (G.ends e).IsDiag → x e ≠ 1)
    (hnoc : ∀ S : Finset V, Odd (S ∩ T).card → ∑ e ∈ G.cut S, x e = 1 →
      (S ∩ Act G T).card ≤ 1 ∨ (Sᶜ ∩ Act G T).card ≤ 1) :
    (∀ v, v ∈ T → ∑ e ∈ G.cut {v}, x e = 1 →
       ((Finset.univ.filter (fun e => 0 < x e ∧ x e < 1)).filter
         (fun e => e ∈ G.cut {v})).card = 2) ∧
    (∀ e, 0 < x e → x e < 1 → ∀ a b, G.ends e = s(a, b) →
       (a ∈ T ∧ ∑ g ∈ G.cut {a}, x g = 1) ∧ (b ∈ T ∧ ∑ g ∈ G.cut {b}, x g = 1)) := by
  classical
  have hxQ := (mem_extremePoints.1 hx).1
  have hcard := card_frac_le G T hT x hx hnoc
  set Ep := Finset.univ.filter (fun e => 0 < x e ∧ x e < 1) with hEp
  set Tt := Finset.univ.filter (fun v => v ∈ T ∧ ∑ e ∈ G.cut {v}, x e = 1) with hTt
  have hf2 : ∀ v ∈ Tt, 2 ≤ (Ep.filter (fun e => e ∈ G.cut {v})).card := fun v hv =>
    frac_ge_two G T x hxQ hno1 v (Finset.mem_filter.1 hv).2.2
  have hsub : ∀ e a b, G.ends e = s(a, b) →
      Tt.filter (fun v => e ∈ G.cut {v}) ⊆ {a, b} := by
    intro e a b h v hv
    have := (Finset.mem_filter.1 hv).2
    rw [mem_cut_iff G {v} e a b h] at this
    simp only [Finset.mem_singleton] at this
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases this with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact Or.inl h1.symm
    · exact Or.inr h1.symm
  have hg2 : ∀ e ∈ Ep, (Tt.filter (fun v => e ∈ G.cut {v})).card ≤ 2 := by
    intro e _
    obtain ⟨⟨a, b⟩, hab⟩ := Quot.exists_rep (G.ends e)
    exact (Finset.card_le_card (hsub e a b hab.symm)).trans Finset.card_le_two
  have hdc : ∑ v ∈ Tt, (Ep.filter (fun e => e ∈ G.cut {v})).card =
      ∑ e ∈ Ep, (Tt.filter (fun v => e ∈ G.cut {v})).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hA : Tt.card * 2 ≤ ∑ v ∈ Tt, (Ep.filter (fun e => e ∈ G.cut {v})).card := by
    rw [← smul_eq_mul, ← Finset.sum_const]; exact Finset.sum_le_sum hf2
  have hB : ∑ e ∈ Ep, (Tt.filter (fun v => e ∈ G.cut {v})).card ≤ Ep.card * 2 := by
    rw [← smul_eq_mul, ← Finset.sum_const]; exact Finset.sum_le_sum hg2
  refine ⟨fun v hvT hv => ?_, fun e he0 he1 a b hab => ?_⟩
  · have hvTt : v ∈ Tt := Finset.mem_filter.2 ⟨Finset.mem_univ _, hvT, hv⟩
    by_contra hne
    have hlt : ∑ w ∈ Tt, 2 < ∑ w ∈ Tt, (Ep.filter (fun e => e ∈ G.cut {w})).card :=
      Finset.sum_lt_sum hf2 ⟨v, hvTt, lt_of_le_of_ne (hf2 v hvTt) (Ne.symm hne)⟩
    rw [Finset.sum_const, smul_eq_mul] at hlt
    omega
  · have heEp : e ∈ Ep := Finset.mem_filter.2 ⟨Finset.mem_univ _, he0, he1⟩
    have hge : (Tt.filter (fun v => e ∈ G.cut {v})).card = 2 := by
      by_contra hne
      have hlt : ∑ e ∈ Ep, (Tt.filter (fun v => e ∈ G.cut {v})).card < ∑ e ∈ Ep, 2 :=
        Finset.sum_lt_sum hg2 ⟨e, heEp, lt_of_le_of_ne (hg2 e heEp) hne⟩
      rw [Finset.sum_const, smul_eq_mul] at hlt
      omega
    have heq : Tt.filter (fun v => e ∈ G.cut {v}) = {a, b} :=
      Finset.eq_of_subset_of_card_le (hsub e a b hab)
        (by rw [hge]; exact Finset.card_le_two)
    have ha : a ∈ Tt.filter (fun v => e ∈ G.cut {v}) := by rw [heq]; simp
    have hb : b ∈ Tt.filter (fun v => e ∈ G.cut {v}) := by rw [heq]; simp
    exact ⟨(Finset.mem_filter.1 (Finset.mem_filter.1 ha).1).2,
      (Finset.mem_filter.1 (Finset.mem_filter.1 hb).1).2⟩

-- ===== L4 part 7 (session 3): case (d) =====
lemma ends_of_cut_single (G : Graph V E) (v : V) (e : E) (he : e ∈ G.cut {v}) :
    ∃ w, w ≠ v ∧ G.ends e = s(v, w) := by
  obtain ⟨⟨a, b⟩, hab⟩ := Quot.exists_rep (G.ends e)
  have h : G.ends e = s(a, b) := hab.symm
  rw [mem_cut_iff G {v} e a b h] at he
  simp only [Finset.mem_singleton] at he
  rcases he with ⟨h1, hb⟩ | ⟨h1, ha⟩
  · subst h1; exact ⟨b, hb, h⟩
  · subst h1; exact ⟨a, ha, h.trans Sym2.eq_swap⟩

lemma mem_cut_single_iff (G : Graph V E) (e : E) (a b y : V) (h : G.ends e = s(a, b))
    (hab : a ≠ b) : e ∈ G.cut {y} ↔ y = a ∨ y = b := by
  rw [mem_cut_iff G {y} e a b h]
  simp only [Finset.mem_singleton]
  constructor
  · rintro (⟨h1, _⟩ | ⟨h1, _⟩)
    · exact Or.inl h1.symm
    · exact Or.inr h1.symm
  · rintro (h1 | h1)
    · exact Or.inl ⟨h1.symm, fun h2 => hab (h1.symm.trans h2.symm)⟩
    · exact Or.inr ⟨h1.symm, fun h2 => hab (h2.trans h1)⟩

lemma cut_single_of_cut (G : Graph V E) (W : Finset V) (e : E) (he : e ∈ G.cut W) :
    ∃ a ∈ W, e ∈ G.cut {a} := by
  obtain ⟨⟨a, b⟩, hab⟩ := Quot.exists_rep (G.ends e)
  have h : G.ends e = s(a, b) := hab.symm
  rw [mem_cut_iff G W e a b h] at he
  rcases he with ⟨ha, hb⟩ | ⟨hb, ha⟩
  · refine ⟨a, ha, (mem_cut_iff G {a} e a b h).2 (Or.inl ⟨Finset.mem_singleton_self a, ?_⟩)⟩
    rw [Finset.mem_singleton]; intro h'; rw [h'] at hb; exact hb ha
  · refine ⟨b, hb, (mem_cut_iff G {b} e a b h).2 (Or.inr ⟨Finset.mem_singleton_self b, ?_⟩)⟩
    rw [Finset.mem_singleton]; intro h'; rw [h'] at ha; exact ha hb

lemma not_cut_of_ends (G : Graph V E) (W : Finset V) (e : E) (a b : V) (h : G.ends e = s(a, b))
    (ha : a ∈ W) (hb : b ∈ W) : e ∉ G.cut W := by
  rw [mem_cut_iff G W e a b h]; tauto

lemma cut_iff_of_ends (G : Graph V E) (e f : E) (h : G.ends e = G.ends f) (S : Finset V) :
    e ∈ G.cut S ↔ f ∈ G.cut S := by
  simp only [Graph.cut, Finset.mem_filter, Finset.mem_univ, true_and, h]

lemma pair_of_mem {α : Type*} [DecidableEq α] (s : Finset α) (hs : s.card = 2) (f : α)
    (hf : f ∈ s) : ∃ g, g ≠ f ∧ s = {f, g} := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hs
  rcases Finset.mem_insert.1 hf with h | h
  · rw [h]; exact ⟨b, hab.symm, rfl⟩
  · rw [Finset.mem_singleton] at h; rw [h]
    exact ⟨a, hab, Finset.pair_comm _ _⟩

lemma zero_of_not_frac (G : Graph V E) (T : Finset V) (x : E → ℝ) (hxQ : x ∈ Q G T)
    (hno1 : ∀ e, ¬ (G.ends e).IsDiag → x e ≠ 1) (e : E) (hnd : ¬ (G.ends e).IsDiag)
    (hf : ¬ (0 < x e ∧ x e < 1)) : x e = 0 := by
  have h0 := hxQ.1.2 e
  have h1 := lt_of_le_of_ne (hxQ.2 e) (hno1 e hnd)
  by_contra hne
  exact hf ⟨lt_of_le_of_ne h0 (Ne.symm hne), h1⟩

lemma cut_sum_le (G : Graph V E) (T : Finset V) (x : E → ℝ) (hxQ : x ∈ Q G T)
    (hno1 : ∀ e, ¬ (G.ends e).IsDiag → x e ≠ 1) (W : Finset V) (L : Finset E)
    (hL : ∀ e ∈ G.cut W, 0 < x e → x e < 1 → e ∈ L) :
    ∑ e ∈ G.cut W, x e ≤ ∑ e ∈ L, x e := by
  classical
  calc ∑ e ∈ G.cut W, x e = ∑ e ∈ (G.cut W).filter (fun e => 0 < x e ∧ x e < 1), x e := by
        refine (Finset.sum_subset (Finset.filter_subset _ _) (fun e he hn => ?_)).symm
        have : ¬ (0 < x e ∧ x e < 1) := fun h => hn (Finset.mem_filter.2 ⟨he, h⟩)
        exact zero_of_not_frac G T x hxQ hno1 e (nonloop_of_cut G W e he) this
    _ ≤ ∑ e ∈ L, x e := Finset.sum_le_sum_of_subset_of_nonneg
        (fun e he => hL e (Finset.mem_filter.1 he).1 (Finset.mem_filter.1 he).2.1
          (Finset.mem_filter.1 he).2.2)
        (fun e _ _ => hxQ.1.2 e)

lemma pair_sum (G : Graph V E) (T : Finset V) (x : E → ℝ) (hxQ : x ∈ Q G T)
    (hno1 : ∀ e, ¬ (G.ends e).IsDiag → x e ≠ 1) (v : V) (hv : ∑ e ∈ G.cut {v}, x e = 1)
    (f g : E) (hgf : g ≠ f)
    (hP : (Finset.univ.filter (fun e => 0 < x e ∧ x e < 1)).filter
      (fun e => e ∈ G.cut {v}) = {f, g}) :
    x f + x g = 1 := by
  rw [← hv, ← Finset.sum_pair hgf.symm, ← hP]
  refine Finset.sum_subset (fun e he => (Finset.mem_filter.1 he).2) (fun e he hn => ?_)
  have : ¬ (0 < x e ∧ x e < 1) := fun h =>
    hn (Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩, he⟩)
  exact zero_of_not_frac G T x hxQ hno1 e (nonloop_of_cut G {v} e he) this

lemma pert_star (G : Graph V E) (T : Finset V) (hT : Even T.card) (x : E → ℝ)
    (hx : x ∈ (Q G T).extremePoints ℝ)
    (hnoc : ∀ S : Finset V, Odd (S ∩ T).card → ∑ e ∈ G.cut S, x e = 1 →
      (S ∩ Act G T).card ≤ 1 ∨ (Sᶜ ∩ Act G T).card ≤ 1)
    (d : E → ℝ) (hd : ∀ e, d e ≠ 0 → 0 < x e ∧ x e < 1)
    (hy : ∀ y, ∑ e ∈ G.cut {y}, d e = 0) : d = 0 := by
  refine perturb_zero G T x hx d hd (fun S hS ht => ?_)
  obtain ⟨y, _, hy'⟩ := tight_star G T hT S hS (hnoc S hS ht)
  rw [hy']; exact hy y

def indE (f : E) : E → ℝ := fun e => if e = f then 1 else 0

lemma sum_indE (K : Finset E) (f : E) : ∑ e ∈ K, indE f e = if f ∈ K then 1 else 0 := by
  simp [indE]

lemma case_d (G : Graph V E) (T : Finset V) (hT : Even T.card) (x : E → ℝ)
    (hx : x ∈ (Q G T).extremePoints ℝ) (hno1 : ∀ e, ¬ (G.ends e).IsDiag → x e ≠ 1)
    (hnoc : ∀ S : Finset V, Odd (S ∩ T).card → ∑ e ∈ G.cut S, x e = 1 →
      (S ∩ Act G T).card ≤ 1 ∨ (Sᶜ ∩ Act G T).card ≤ 1) :
    ∃ F : Finset E, x = charV F := by
  classical
  have hxQ := (mem_extremePoints.1 hx).1
  obtain ⟨D1, D2⟩ := deg_two G T hT x hx hno1 hnoc
  by_cases hE : ∃ e, 0 < x e ∧ x e < 1
  swap
  · push_neg at hE
    refine ⟨Finset.univ.filter (fun e => x e = 1), funext fun e => ?_⟩
    simp only [charV, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs with h
    · exact h
    · have h0 := hxQ.1.2 e
      have h1 := lt_of_le_of_ne (hxQ.2 e) h
      by_contra hne
      exact absurd h1 (not_lt.2 (hE e (lt_of_le_of_ne h0 (Ne.symm hne))))
  obtain ⟨e1, he1⟩ := hE
  have hmem : ∀ (a : V) (e : E), 0 < x e → x e < 1 → e ∈ G.cut {a} →
      e ∈ (Finset.univ.filter (fun e => 0 < x e ∧ x e < 1)).filter (fun e => e ∈ G.cut {a}) :=
    fun a e h0 h1 hc => Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, h0, h1⟩, hc⟩
  have inP : ∀ (a : V) (e f g : E),
      (Finset.univ.filter (fun e => 0 < x e ∧ x e < 1)).filter (fun e => e ∈ G.cut {a}) =
        {f, g} → 0 < x e → x e < 1 → e ∈ G.cut {a} → e = f ∨ e = g := by
    intro a e f g hfg h0 h1 hc
    have hm := hmem a e h0 h1 hc
    rw [hfg] at hm
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have ofP : ∀ (a : V) (f g : E),
      (Finset.univ.filter (fun e => 0 < x e ∧ x e < 1)).filter (fun e => e ∈ G.cut {a}) =
        {f, g} → (0 < x g ∧ x g < 1) ∧ g ∈ G.cut {a} := by
    intro a f g hfg
    have hm : g ∈ (Finset.univ.filter (fun e => 0 < x e ∧ x e < 1)).filter
        (fun e => e ∈ G.cut {a}) := by rw [hfg]; simp
    obtain ⟨hm1, hm2⟩ := Finset.mem_filter.1 hm
    exact ⟨(Finset.mem_filter.1 hm1).2, hm2⟩
  have hnl : ∀ e, 0 < x e → x e < 1 → ¬ (G.ends e).IsDiag := by
    intro e h0 h1 hd
    rcases loop_int G T x hx e hd with h | h <;> linarith
  obtain ⟨⟨v, u⟩, hq1⟩ := Quot.exists_rep (G.ends e1)
  have h1 : G.ends e1 = s(v, u) := hq1.symm
  have hvu : v ≠ u := by
    intro h; apply hnl e1 he1.1 he1.2; rw [h1, h]; exact Sym2.mk_isDiag_iff.2 rfl
  obtain ⟨⟨hvT, hvt⟩, ⟨huT, hut⟩⟩ := D2 e1 he1.1 he1.2 v u h1
  have he1v : e1 ∈ G.cut {v} := (mem_cut_single_iff G e1 v u v h1 hvu).2 (Or.inl rfl)
  have he1u : e1 ∈ G.cut {u} := (mem_cut_single_iff G e1 v u u h1 hvu).2 (Or.inr rfl)
  obtain ⟨e2, he21, hPv⟩ := pair_of_mem _ (D1 v hvT hvt) e1 (hmem v e1 he1.1 he1.2 he1v)
  obtain ⟨he2, he2v⟩ := ofP v e1 e2 hPv
  obtain ⟨w, hwv, h2⟩ := ends_of_cut_single G v e2 he2v
  obtain ⟨-, ⟨hwT, hwt⟩⟩ := D2 e2 he2.1 he2.2 v w h2
  have hxv := pair_sum G T x hxQ hno1 v hvt e1 e2 he21 hPv
  by_cases huw : u = w
  · -- two parallel fractional edges
    have h2' : G.ends e2 = s(v, u) := by rw [huw]; exact h2
    have hiff : ∀ S, e1 ∈ G.cut S ↔ e2 ∈ G.cut S := cut_iff_of_ends G e1 e2 (h1.trans h2'.symm)
    have hdf : ∀ e, (indE e1 - indE e2) e ≠ 0 → 0 < x e ∧ x e < 1 := by
      intro e he
      by_cases a1 : e = e1
      · rw [a1]; exact he1
      by_cases a2 : e = e2
      · rw [a2]; exact he2
      exact (he (by simp [indE, a1, a2])).elim
    have hdy : ∀ y, ∑ e ∈ G.cut {y}, (indE e1 - indE e2) e = 0 := by
      intro y
      simp only [Pi.sub_apply, Finset.sum_sub_distrib, sum_indE, hiff, sub_self]
    have hd0 := pert_star G T hT x hx hnoc _ hdf hdy
    have := congrFun hd0 e1
    simp [indE, Ne.symm he21] at this
  obtain ⟨e3, he31, hPu⟩ := pair_of_mem _ (D1 u huT hut) e1 (hmem u e1 he1.1 he1.2 he1u)
  obtain ⟨he3, he3u⟩ := ofP u e1 e3 hPu
  obtain ⟨z1, hz1u, h3⟩ := ends_of_cut_single G u e3 he3u
  have he2w : e2 ∈ G.cut {w} := (mem_cut_single_iff G e2 v w w h2 hwv.symm).2 (Or.inr rfl)
  obtain ⟨e4, he42, hPw⟩ := pair_of_mem _ (D1 w hwT hwt) e2 (hmem w e2 he2.1 he2.2 he2w)
  obtain ⟨he4, he4w⟩ := ofP w e2 e4 hPw
  obtain ⟨z2, hz2w, h4⟩ := ends_of_cut_single G w e4 he4w
  have hxu := pair_sum G T x hxQ hno1 u hut e1 e3 he31 hPu
  have hxw := pair_sum G T x hxQ hno1 w hwt e2 e4 he42 hPw
  have hz1v : z1 ≠ v := by
    intro hz
    have hc : e3 ∈ G.cut {v} :=
      (mem_cut_single_iff G e3 u z1 v h3 hz1u.symm).2 (Or.inr hz.symm)
    rcases inP v e3 e1 e2 hPv he3.1 he3.2 hc with h | h
    · exact he31 h
    · rw [h, h2] at h3
      rcases Sym2.eq_iff.1 h3 with ⟨a, _⟩ | ⟨_, b⟩
      · exact hvu a
      · exact huw b.symm
  have hz2v : z2 ≠ v := by
    intro hz
    have hc : e4 ∈ G.cut {v} :=
      (mem_cut_single_iff G e4 w z2 v h4 hz2w.symm).2 (Or.inr hz.symm)
    rcases inP v e4 e1 e2 hPv he4.1 he4.2 hc with h | h
    · rw [h, h1] at h4
      rcases Sym2.eq_iff.1 h4 with ⟨a, _⟩ | ⟨_, b⟩
      · exact hwv a.symm
      · exact huw b
    · exact he42 h
  have hcutW : ∀ e ∈ G.cut {v, u, w}, 0 < x e → x e < 1 → e = e3 ∨ e = e4 := by
    intro e hc h0 h1'
    obtain ⟨a, ha, hca⟩ := cut_single_of_cut G _ e hc
    have nW1 := not_cut_of_ends G {v, u, w} e1 v u h1 (by simp) (by simp)
    have nW2 := not_cut_of_ends G {v, u, w} e2 v w h2 (by simp) (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with ha | ha | ha <;> rw [ha] at hca
    · rcases inP v e e1 e2 hPv h0 h1' hca with h | h
      · rw [h] at hc; exact absurd hc nW1
      · rw [h] at hc; exact absurd hc nW2
    · rcases inP u e e1 e3 hPu h0 h1' hca with h | h
      · rw [h] at hc; exact absurd hc nW1
      · exact Or.inl h
    · rcases inP w e e2 e4 hPw h0 h1' hca with h | h
      · rw [h] at hc; exact absurd hc nW2
      · exact Or.inr h
  have hW3 : ({v, u, w} : Finset V).card = 3 :=
    Finset.card_eq_three.2 ⟨v, u, w, hvu, hwv.symm, huw, rfl⟩
  have hWT : ({v, u, w} : Finset V) ∩ T = {v, u, w} :=
    Finset.inter_eq_left.2 (by simp [Finset.insert_subset_iff, hvT, huT, hwT])
  have hWodd : Odd (({v, u, w} : Finset V) ∩ T).card := by rw [hWT, hW3]; exact ⟨1, rfl⟩
  have hfeas := hxQ.1.1 _ hWodd
  by_cases hz1w : z1 = w
  · -- triangle: the odd set {v,u,w} has an empty fractional cut
    have h3' : G.ends e3 = s(u, w) := by rw [← hz1w]; exact h3
    have nW3 := not_cut_of_ends G {v, u, w} e3 u w h3' (by simp) (by simp)
    have he3w : e3 ∈ G.cut {w} := (mem_cut_single_iff G e3 u w w h3' huw).2 (Or.inr rfl)
    have he34 : e3 = e4 := by
      rcases inP w e3 e2 e4 hPw he3.1 he3.2 he3w with h | h
      · rw [h, h2] at h3'
        rcases Sym2.eq_iff.1 h3' with ⟨a, _⟩ | ⟨a, _⟩
        · exact (hvu a).elim
        · exact (hwv a.symm).elim
      · exact h
    have hle := cut_sum_le G T x hxQ hno1 {v, u, w} ∅ (fun e hc h0 h1' => by
      rcases hcutW e hc h0 h1' with h | h
      · rw [h] at hc; exact absurd hc nW3
      · rw [h, ← he34] at hc; exact absurd hc nW3)
    rw [Finset.sum_empty] at hle
    linarith
  have hz2u : z2 ≠ u := by
    intro hz
    have hc : e4 ∈ G.cut {u} :=
      (mem_cut_single_iff G e4 w z2 u h4 hz2w.symm).2 (Or.inr hz.symm)
    rcases inP u e4 e1 e3 hPu he4.1 he4.2 hc with h | h
    · rw [h, h1] at h4
      rcases Sym2.eq_iff.1 h4 with ⟨a, _⟩ | ⟨_, b⟩
      · exact hwv a.symm
      · exact huw b
    · rw [h, h3] at h4
      rcases Sym2.eq_iff.1 h4 with ⟨a, _⟩ | ⟨_, b⟩
      · exact huw a
      · exact hz1w b
  have he34 : e3 ≠ e4 := by
    intro h; rw [h, h4] at h3
    rcases Sym2.eq_iff.1 h3 with ⟨a, _⟩ | ⟨a, _⟩
    · exact huw a.symm
    · exact hz1w a.symm
  have hle := cut_sum_le G T x hxQ hno1 {v, u, w} {e3, e4} (fun e hc h0 h1' => by
    rcases hcutW e hc h0 h1' with h | h <;> rw [h] <;> simp)
  rw [Finset.sum_pair he34] at hle
  have htight : ∑ e ∈ G.cut {v, u, w}, x e = 1 := by linarith
  have hAv := act_of_end G T e1 v u h1 hvu
  have hAw := act_of_end G T e2 v w h2 hwv.symm
  have hA3 := act_of_end G T e3 u z1 h3 hz1u.symm
  have hA4 := act_of_end G T e4 w z2 h4 hz2w.symm
  have hz : z1 = z2 := by
    rcases hnoc _ hWodd htight with hc | hc
    · have hsub : ({v, u, w} : Finset V) ⊆ {v, u, w} ∩ Act G T := by
        intro a ha
        refine Finset.mem_inter.2 ⟨ha, ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with ha | ha | ha <;> rw [ha]
        · exact hAv.1
        · exact hAv.2
        · exact hAw.2
      have := Finset.card_le_card hsub
      omega
    · refine Finset.card_le_one.1 hc z1 ?_ z2 ?_
      · refine Finset.mem_inter.2 ⟨?_, hA3.2⟩
        simp [hz1v, hz1u, hz1w]
      · refine Finset.mem_inter.2 ⟨?_, hA4.2⟩
        simp [hz2v, hz2u, hz2w]
  rw [← hz] at h4
  -- four-cycle v - u - z1 - w - v: alternating perturbation
  have hdf : ∀ e, (indE e1 - indE e2 - indE e3 + indE e4) e ≠ 0 → 0 < x e ∧ x e < 1 := by
    intro e he
    by_cases a1 : e = e1
    · rw [a1]; exact he1
    by_cases a2 : e = e2
    · rw [a2]; exact he2
    by_cases a3 : e = e3
    · rw [a3]; exact he3
    by_cases a4 : e = e4
    · rw [a4]; exact he4
    exact (he (by simp [indE, a1, a2, a3, a4])).elim
  have hdy : ∀ y, ∑ e ∈ G.cut {y}, (indE e1 - indE e2 - indE e3 + indE e4) e = 0 := by
    intro y
    simp only [Pi.add_apply, Pi.sub_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      sum_indE, mem_cut_single_iff G e1 v u y h1 hvu,
      mem_cut_single_iff G e2 v w y h2 hwv.symm,
      mem_cut_single_iff G e3 u z1 y h3 hz1u.symm,
      mem_cut_single_iff G e4 w z1 y h4 (Ne.symm hz1w)]
    by_cases a1 : y = v
    · simp [a1, hvu, hwv.symm, Ne.symm hz1v]
    by_cases a2 : y = u
    · simp [a2, hvu.symm, huw, Ne.symm hz1u]
    by_cases a3 : y = w
    · simp [a3, hwv, Ne.symm huw, Ne.symm hz1w]
    by_cases a4 : y = z1
    · simp [a4, hz1v, hz1u, hz1w]
    simp [a1, a2, a3, a4]
  have hd0 := pert_star G T hT x hx hnoc _ hdf hdy
  have h14 : e1 ≠ e4 := by
    intro h; rw [h, h4] at h1
    rcases Sym2.eq_iff.1 h1 with ⟨a, _⟩ | ⟨a, _⟩
    · exact hwv a
    · exact huw a.symm
  have := congrFun hd0 e1
  simp [indE, Ne.symm he21, Ne.symm he31, h14] at this

end CombOpt.TJoin.R528

open CombOpt.TJoin in
theorem solution {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : CombOpt.TJoin.Graph V E) (T : Finset V) (hT : Even T.card) (c : E → ℝ) (hc : ∀ e, 0 ≤ c e) :
    G.minTJoinCost T c = G.lpValue533 T c := by
  exact CombOpt.TJoin.R528.main G T c (CombOpt.TJoin.R528.keyDom_of_extreme G T c hc
    (fun x hx => CombOpt.TJoin.R528.L4_of CombOpt.TJoin.R528.case_d _ G T rfl hT x hx))
