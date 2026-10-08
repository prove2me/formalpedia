-- Prove2me | solution 1 for DiscreteConvex.NetworkFlowsB.negative_cycle_criterion_mcfp0
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T01:21:33.107977+00:00
-- url     : https://prove2.me/submissions/6c1f5c26-7082-4e7d-868b-e965906a1e04

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_FeasibleFlowMCFP0
import Definitions.Def_DiscreteConvex_NetworkFlowsB_OptimalFlowMCFP0
import Definitions.Def_DiscreteConvex_NetworkFlowsB_HasNegativeCycle
import Definitions.Def_DiscreteConvex_NetworkFlowsB_AuxTailMCFP0
import Definitions.Def_DiscreteConvex_NetworkFlowsB_AuxHeadMCFP0
import Definitions.Def_DiscreteConvex_NetworkFlowsB_AuxActiveMCFP0
import Definitions.Def_DiscreteConvex_NetworkFlowsB_AuxLengthMCFP0

open Classical
open scoped Pointwise

namespace DiscreteConvex.NetworkFlowsB

section NC
set_option linter.unusedSectionVars false

variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

def evA : A ⊕ A → A → ℝ
  | .inl a => fun b => if a = b then 1 else 0
  | .inr a => fun b => if a = b then -1 else 0

def lenR (gamma : A → ℝ) : A ⊕ A → ℝ
  | .inl a => gamma a
  | .inr a => -gamma a

def chiC {k : ℕ} (c : Fin (k+1) → A ⊕ A) : A → ℝ := fun b => ∑ i, evA (c i) b

lemma boundary_sum {ι : Type*} [Fintype ι] (tail head : A → V) (g : ι → A → ℝ) (v : V) :
    Boundary tail head (fun b => ∑ i, g i b) v = ∑ i, Boundary tail head (g i) v := by
  unfold Boundary; rw [Finset.sum_sub_distrib]; congr 1 <;> exact Finset.sum_comm

lemma boundary_lin (tail head : A → V) (d g : A → ℝ) (e : ℝ) (v : V) :
    Boundary tail head (fun b => d b + e * g b) v =
      Boundary tail head d v + e * Boundary tail head g v := by
  simp only [Boundary, Finset.sum_add_distrib, ← Finset.mul_sum]; ring

lemma boundary_evA (tail head : A → V) (e : A ⊕ A) (v : V) :
    Boundary tail head (evA e) v =
      (if AuxTailMCFP0 tail head e = v then 1 else 0) -
        (if AuxHeadMCFP0 tail head e = v then 1 else 0) := by
  cases e with
  | inl a =>
    simp [Boundary, evA, AuxTailMCFP0, AuxHeadMCFP0, Finset.sum_ite_eq]
    split_ifs <;> simp_all
  | inr a =>
    simp [Boundary, evA, AuxTailMCFP0, AuxHeadMCFP0, Finset.sum_ite_eq]
    split_ifs <;> simp_all

lemma boundary_chi (tail head : A → V) {k : ℕ} (c : Fin (k+1) → A ⊕ A)
    (hc : IsCycle (AuxTailMCFP0 tail head) (AuxHeadMCFP0 tail head) k c) :
    Boundary tail head (chiC c) = 0 := by
  funext v
  unfold chiC
  rw [boundary_sum]
  simp_rw [boundary_evA]
  rw [Finset.sum_sub_distrib, Pi.zero_apply, sub_eq_zero]
  have h : ∀ i, AuxHeadMCFP0 tail head (c i) = AuxTailMCFP0 tail head (c (i+1)) := hc
  simp_rw [h]
  exact (Fintype.sum_equiv (Equiv.addRight (1 : Fin (k+1)))
    (fun i => if AuxTailMCFP0 tail head (c (i+1)) = v then (1:ℝ) else 0)
    (fun i => if AuxTailMCFP0 tail head (c i) = v then (1:ℝ) else 0) (fun i => rfl)).symm

lemma cost_evA (gamma : A → ℝ) (e : A ⊕ A) : ∑ b, gamma b * evA e b = lenR gamma e := by
  cases e <;> simp [evA, lenR]

lemma cost_chi (gamma : A → ℝ) {k : ℕ} (c : Fin (k+1) → A ⊕ A) :
    ∑ b, gamma b * chiC c b = ∑ i, lenR gamma (c i) := by
  simp only [chiC, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [cost_evA]

lemma cycleLength_eq (gamma : A → ℝ) {k : ℕ} (c : Fin (k+1) → A ⊕ A) :
    CycleLength (AuxLengthMCFP0 gamma) k c = ((∑ i, lenR gamma (c i) : ℝ) : WithTop ℝ) := by
  unfold CycleLength
  push_cast
  refine Finset.sum_congr rfl (fun i _ => ?_)
  cases c i <;> rfl

lemma feas0_iff (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (gamma : A → ℝ) (x : V → ℝ) (xi : A → ℝ) :
    FeasibleFlowMCFP0 tail head cUpper cLower gamma x xi ↔
      (∀ a, cLower a ≤ (xi a : WithBot ℝ) ∧ (xi a : WithTop ℝ) ≤ cUpper a) ∧
        Boundary tail head xi = x := by
  unfold FeasibleFlowMCFP0 FeasibleFlowMCFP3 ArcCostMCFP0 BoundaryCostMCFP0
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun a => ?_, ?_⟩
    · have := h1 a; by_contra hc; exact this (if_neg hc)
    · by_contra hc; exact h2 (if_neg hc)
  · rintro ⟨h1, h2⟩
    exact ⟨fun a => by rw [if_pos (h1 a)]; exact WithTop.coe_ne_top, by
      rw [if_pos h2]; exact WithTop.zero_ne_top⟩

lemma gam0 (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (gamma : A → ℝ) (x : V → ℝ) (xi : A → ℝ)
    (h : FeasibleFlowMCFP0 tail head cUpper cLower gamma x xi) :
    Gamma3 tail head (ArcCostMCFP0 cUpper cLower gamma) (BoundaryCostMCFP0 x) xi =
      ((∑ a, gamma a * xi a : ℝ) : WithTop ℝ) := by
  rw [feas0_iff] at h
  unfold Gamma3 ArcCostMCFP0 BoundaryCostMCFP0
  rw [if_pos h.2, add_zero]
  push_cast
  exact Finset.sum_congr rfl (fun a _ => by rw [if_pos (h.1 a)])


lemma ev_top (c : WithTop ℝ) (t : ℝ) (h : (t : WithTop ℝ) < c) :
    ∀ᶠ s : ℝ in nhds t, (s : WithTop ℝ) ≤ c := by
  induction c using WithTop.recTopCoe with
  | top => exact Filter.Eventually.of_forall (fun _ => le_top)
  | coe u =>
    have : t < u := by exact_mod_cast h
    filter_upwards [gt_mem_nhds this] with s hs
    exact_mod_cast hs.le

lemma ev_bot (c : WithBot ℝ) (t : ℝ) (h : c < (t : WithBot ℝ)) :
    ∀ᶠ s : ℝ in nhds t, c ≤ (s : WithBot ℝ) := by
  induction c using WithBot.recBotCoe with
  | bot => exact Filter.Eventually.of_forall (fun _ => bot_le)
  | coe u =>
    have : u < t := by exact_mod_cast h
    filter_upwards [lt_mem_nhds this] with s hs
    exact_mod_cast hs.le

lemma ev_comp (P : ℝ → Prop) (t g : ℝ) (h : ∀ᶠ s in nhds t, P s) :
    ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0), P (t + ε * g) := by
  have hc : Continuous (fun ε : ℝ => t + ε * g) := by fun_prop
  have ht := hc.tendsto 0
  simp only [zero_mul, add_zero] at ht
  exact (ht.eventually h).filter_mono nhdsWithin_le_nhds

lemma opt_no_negcycle (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (gamma : A → ℝ) (x : V → ℝ) (xi : A → ℝ)
    (ho : OptimalFlowMCFP0 tail head cUpper cLower gamma x xi) :
    ¬ HasNegativeCycle (AuxTailMCFP0 tail head) (AuxHeadMCFP0 tail head)
        (AuxActiveMCFP0 cUpper cLower xi) (AuxLengthMCFP0 gamma) := by
  rintro ⟨k, c, hact, hcyc, hneg⟩
  have hfe : FeasibleFlowMCFP0 tail head cUpper cLower gamma x xi := ho.1
  have hfe' := (feas0_iff tail head cUpper cLower gamma x xi).1 hfe
  rw [cycleLength_eq] at hneg
  have hL : ∑ i, lenR gamma (c i) < 0 := by exact_mod_cast hneg
  set χ := chiC c with hχ
  have hpos : ∀ b, 0 < χ b → (xi b : WithTop ℝ) < cUpper b := by
    intro b hb
    by_contra hcon
    have : ∀ i, evA (c i) b ≤ 0 := by
      intro i
      have := hact i
      cases hci : c i with
      | inl a =>
        rw [hci] at this
        simp only [evA]
        split_ifs with hab
        · subst hab; exact absurd this hcon
        · exact le_rfl
      | inr a => simp only [evA]; split_ifs <;> norm_num
    have : χ b ≤ 0 := Finset.sum_nonpos (fun i _ => this i)
    linarith
  have hnegc : ∀ b, χ b < 0 → cLower b < (xi b : WithBot ℝ) := by
    intro b hb
    by_contra hcon
    have : ∀ i, 0 ≤ evA (c i) b := by
      intro i
      have := hact i
      cases hci : c i with
      | inr a =>
        rw [hci] at this
        simp only [evA]
        split_ifs with hab
        · subst hab; exact absurd this hcon
        · exact le_rfl
      | inl a => simp only [evA]; split_ifs <;> norm_num
    have : 0 ≤ χ b := Finset.sum_nonneg (fun i _ => this i)
    linarith
  have hev : ∀ b, ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0),
      cLower b ≤ ((xi b + ε * χ b : ℝ) : WithBot ℝ) ∧
        ((xi b + ε * χ b : ℝ) : WithTop ℝ) ≤ cUpper b := by
    intro b
    have hup : ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0),
        ((xi b + ε * χ b : ℝ) : WithTop ℝ) ≤ cUpper b := by
      by_cases hb : 0 < χ b
      · exact ev_comp (fun s => (s : WithTop ℝ) ≤ cUpper b) (xi b) (χ b)
          (ev_top _ _ (hpos b hb))
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        have hε' : (0:ℝ) < ε := hε
        refine le_trans ?_ (hfe'.1 b).2
        have : xi b + ε * χ b ≤ xi b := by nlinarith
        exact_mod_cast this
    have hlo : ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0),
        cLower b ≤ ((xi b + ε * χ b : ℝ) : WithBot ℝ) := by
      by_cases hb : χ b < 0
      · exact ev_comp (fun s => cLower b ≤ (s : WithBot ℝ)) (xi b) (χ b)
          (ev_bot _ _ (hnegc b hb))
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        have hε' : (0:ℝ) < ε := hε
        refine le_trans (hfe'.1 b).1 ?_
        have : xi b ≤ xi b + ε * χ b := by nlinarith
        exact_mod_cast this
    exact hlo.and hup
  obtain ⟨ε, hε, hεpos⟩ := ((Filter.eventually_all.2 hev).and self_mem_nhdsWithin).exists
  have hε0 : (0:ℝ) < ε := hεpos
  have hf' : FeasibleFlowMCFP0 tail head cUpper cLower gamma x (fun b => xi b + ε * χ b) := by
    rw [feas0_iff]
    refine ⟨hε, ?_⟩
    funext v
    rw [boundary_lin, hχ, boundary_chi tail head c hcyc, hfe'.2]
    simp
  have h1 := ho.2 _ hf'
  rw [gam0 tail head cUpper cLower gamma x xi hfe, gam0 tail head cUpper cLower gamma x _ hf',
    WithTop.coe_le_coe] at h1
  have hcost : ∑ a, gamma a * (xi a + ε * χ a) = ∑ a, gamma a * xi a + ε * ∑ i, lenR gamma (c i) := by
    rw [← cost_chi, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun a _ => by ring)
  rw [hcost] at h1
  nlinarith


def posArc (d : A → ℝ) : A ⊕ A → Prop
  | .inl b => 0 < d b
  | .inr b => d b < 0

lemma exists_next (tail head : A → V) (d : A → ℝ) (hd : Boundary tail head d = 0)
    (e : A ⊕ A) (he : posArc d e) :
    ∃ e', posArc d e' ∧ AuxTailMCFP0 tail head e' = AuxHeadMCFP0 tail head e := by
  by_contra hcon
  push_neg at hcon
  have h1 : ∀ b ∈ Finset.univ.filter (fun b => tail b = AuxHeadMCFP0 tail head e), d b ≤ 0 := by
    intro b hb; simp only [Finset.mem_filter] at hb
    by_contra h; push_neg at h
    exact hcon (.inl b) h hb.2
  have h2 : ∀ b ∈ Finset.univ.filter (fun b => head b = AuxHeadMCFP0 tail head e), 0 ≤ d b := by
    intro b hb; simp only [Finset.mem_filter] at hb
    by_contra h; push_neg at h
    exact hcon (.inr b) h hb.2
  have hbv := congrFun hd (AuxHeadMCFP0 tail head e)
  simp only [Boundary, Pi.zero_apply] at hbv
  have s1 := Finset.sum_nonpos h1
  have s2 := Finset.sum_nonneg h2
  have e1 : ∑ b ∈ Finset.univ.filter (fun b => tail b = AuxHeadMCFP0 tail head e), d b = 0 := by
    linarith
  have e2 : ∑ b ∈ Finset.univ.filter (fun b => head b = AuxHeadMCFP0 tail head e), d b = 0 := by
    linarith
  cases e with
  | inl b =>
    have := (Finset.sum_eq_zero_iff_of_nonneg h2).1 e2 b (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩)
    simp only [posArc] at he; linarith
  | inr b =>
    have := (Finset.sum_eq_zero_iff_of_nonpos h1).1 e1 b (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩)
    simp only [posArc] at he; linarith

lemma extract (tail head : A → V) (gamma : A → ℝ) (R : A ⊕ A → Prop) :
    ∀ n, ∀ d : A → ℝ, (Finset.univ.filter (fun b => d b ≠ 0)).card = n →
      Boundary tail head d = 0 → ∑ b, gamma b * d b < 0 → (∀ e, posArc d e → R e) →
      ∃ k, ∃ c : Fin (k+1) → A ⊕ A, (∀ i, R (c i)) ∧
        IsCycle (AuxTailMCFP0 tail head) (AuxHeadMCFP0 tail head) k c ∧
        ∑ i, lenR gamma (c i) < 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro d hn hd hcost hR
  obtain ⟨b0, hb0⟩ : ∃ b, d b ≠ 0 := by
    by_contra h; push_neg at h; simp [h] at hcost
  obtain ⟨e0, he0⟩ : ∃ e, posArc d e := by
    rcases lt_or_gt_of_ne hb0 with h | h
    · exact ⟨.inr b0, h⟩
    · exact ⟨.inl b0, h⟩
  choose! nx hnxS hnxT using exists_next tail head d hd
  have hsS : ∀ m, posArc d (nx^[m] e0) := by
    intro m; induction m with
    | zero => exact he0
    | succ m ihm => rw [Function.iterate_succ_apply']; exact hnxS _ ihm
  have hsT : ∀ m, AuxTailMCFP0 tail head (nx^[m+1] e0) = AuxHeadMCFP0 tail head (nx^[m] e0) := by
    intro m; rw [Function.iterate_succ_apply']; exact hnxT _ (hsS m)
  obtain ⟨i, j, hij, heq⟩ : ∃ i j, i < j ∧ nx^[i] e0 = nx^[j] e0 := by
    obtain ⟨i, j, hne, he⟩ := Finite.exists_ne_map_eq_of_infinite (fun m => nx^[m] e0)
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact ⟨i, j, h, he⟩
    · exact ⟨j, i, h, he.symm⟩
  obtain ⟨k, hk⟩ : ∃ k, j = i + k + 1 := ⟨j - i - 1, by omega⟩
  let c : Fin (k+1) → A ⊕ A := fun idx => nx^[i + idx] e0
  have hcR : ∀ idx, posArc d (c idx) := fun idx => hsS _
  have hcyc : IsCycle (AuxTailMCFP0 tail head) (AuxHeadMCFP0 tail head) k c := by
    intro idx
    simp only [c]
    rw [Fin.val_add_one]
    split_ifs with hl
    · rw [hl, Fin.val_last, add_zero, heq, hk]
      exact (hsT _).symm
    · rw [← add_assoc]
      exact (hsT _).symm
  by_cases hneg : ∑ idx, lenR gamma (c idx) < 0
  · exact ⟨k, c, fun idx => hR _ (hcR idx), hcyc, hneg⟩
  push_neg at hneg
  have hterm : ∀ e, posArc d e → ∀ b, (d b ≤ 0 → evA e b ≤ 0) ∧ (0 ≤ d b → 0 ≤ evA e b) := by
    intro e he b
    cases e with
    | inl a =>
      simp only [posArc] at he
      simp only [evA]
      constructor
      · intro hb; split_ifs with h
        · subst h; linarith
        · exact le_rfl
      · intro _; split_ifs <;> norm_num
    | inr a =>
      simp only [posArc] at he
      simp only [evA]
      constructor
      · intro _; split_ifs <;> norm_num
      · intro hb; split_ifs with h
        · subst h; linarith
        · exact le_rfl
  have hχpos : ∀ b, 0 ≤ d b → 0 ≤ chiC c b := fun b hb =>
    Finset.sum_nonneg (fun idx _ => (hterm _ (hcR idx) b).2 hb)
  have hχneg : ∀ b, d b ≤ 0 → chiC c b ≤ 0 := fun b hb =>
    Finset.sum_nonpos (fun idx _ => (hterm _ (hcR idx) b).1 hb)
  have hsign : ∀ b, chiC c b ≠ 0 → (0 < chiC c b ∧ 0 < d b) ∨ (chiC c b < 0 ∧ d b < 0) := by
    intro b hb
    rcases lt_trichotomy (d b) 0 with h|h|h
    · right; exact ⟨lt_of_le_of_ne (hχneg b h.le) hb, h⟩
    · exfalso; exact hb (le_antisymm (hχneg b h.le) (hχpos b h.ge))
    · left; exact ⟨lt_of_le_of_ne (hχpos b h.le) (Ne.symm hb), h⟩
  have hT : ∃ b, chiC c b ≠ 0 := by
    have hc0R := hcR 0
    cases hc0 : c 0 with
    | inl b =>
      refine ⟨b, ne_of_gt ?_⟩
      rw [hc0] at hc0R
      have hdb : 0 < d b := hc0R
      have h1 : evA (c 0) b ≤ chiC c b :=
        Finset.single_le_sum (f := fun idx => evA (c idx) b)
          (fun idx _ => (hterm _ (hcR idx) b).2 hdb.le) (Finset.mem_univ 0)
      rw [hc0] at h1; simp [evA] at h1; linarith
    | inr b =>
      refine ⟨b, ne_of_lt ?_⟩
      rw [hc0] at hc0R
      have hdb : d b < 0 := hc0R
      have h1 : -evA (c 0) b ≤ ∑ idx, -evA (c idx) b :=
        Finset.single_le_sum (f := fun idx => -evA (c idx) b)
          (fun idx _ => by linarith [(hterm _ (hcR idx) b).1 hdb.le]) (Finset.mem_univ 0)
      rw [Finset.sum_neg_distrib, hc0] at h1
      have hv : evA (Sum.inr b : A ⊕ A) b = -1 := by simp [evA]
      rw [hv] at h1
      show ∑ idx, evA (c idx) b < 0
      linarith
  obtain ⟨bT, hbT⟩ := hT
  obtain ⟨bm, hbmT, hbm⟩ := (Finset.univ.filter (fun b => chiC c b ≠ 0)).exists_min_image
    (fun b => d b / chiC c b) ⟨bT, by simp [hbT]⟩
  have hbmχ : chiC c bm ≠ 0 := (Finset.mem_filter.1 hbmT).2
  obtain ⟨ε, hεdef⟩ : ∃ ε, ε = d bm / chiC c bm := ⟨_, rfl⟩
  have hε : 0 < ε := by
    rw [hεdef]
    rcases hsign bm hbmχ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact div_pos h2 h1
    · exact div_pos_of_neg_of_neg h2 h1
  have hd'prop : ∀ b, (0 < d b + (-ε) * chiC c b → 0 < d b) ∧
      (d b + (-ε) * chiC c b < 0 → d b < 0) ∧ (d b + (-ε) * chiC c b ≠ 0 → d b ≠ 0) := by
    intro b
    by_cases hχb : chiC c b = 0
    · simp [hχb]
    · have hle : ε ≤ d b / chiC c b := by
        rw [hεdef]; exact hbm b (by simp [hχb])
      rcases hsign b hχb with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [le_div_iff₀ h1] at hle
        refine ⟨fun _ => h2, fun h => ?_, fun _ => h2.ne'⟩
        nlinarith
      · rw [le_div_iff_of_neg h1] at hle
        refine ⟨fun h => ?_, fun _ => h2, fun _ => h2.ne⟩
        nlinarith
  have hd'bm : d bm + (-ε) * chiC c bm = 0 := by
    have : d bm / chiC c bm * chiC c bm = d bm := div_mul_cancel₀ _ hbmχ
    rw [hεdef]; linear_combination (-1:ℝ) * this
  have hcard : (Finset.univ.filter (fun b => d b + (-ε) * chiC c b ≠ 0)).card < n := by
    rw [← hn]
    apply Finset.card_lt_card
    refine ⟨fun b hb => ?_, fun hsub => ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      exact (hd'prop b).2.2 hb
    · have hm : bm ∈ Finset.univ.filter (fun b => d b ≠ 0) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hsign bm hbmχ with ⟨_, h⟩ | ⟨_, h⟩
        · exact h.ne'
        · exact h.ne
      have := hsub hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this hd'bm
  have hbd' : Boundary tail head (fun b => d b + (-ε) * chiC c b) = 0 := by
    funext v
    rw [boundary_lin, boundary_chi tail head c hcyc, hd]
    simp
  have hcost' : ∑ b, gamma b * (d b + (-ε) * chiC c b) < 0 := by
    have : ∑ b, gamma b * (d b + (-ε) * chiC c b) =
        ∑ b, gamma b * d b + (-ε) * ∑ idx, lenR gamma (c idx) := by
      rw [← cost_chi, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun b _ => by ring)
    rw [this]; nlinarith
  have hR' : ∀ e, posArc (fun b => d b + (-ε) * chiC c b) e → R e := by
    intro e he; apply hR
    cases e with
    | inl b => exact (hd'prop b).1 he
    | inr b => exact (hd'prop b).2.1 he
  exact ih _ hcard _ rfl hbd' hcost' hR'

theorem negative_cycle_criterion_mcfp0_core (tail head : A → V) (cUpper : A → WithTop ℝ)
    (cLower : A → WithBot ℝ) (gamma : A → ℝ) (x : V → ℝ) (xi : A → ℝ)
    (hfeas : FeasibleFlowMCFP0 tail head cUpper cLower gamma x xi) :
    OptimalFlowMCFP0 tail head cUpper cLower gamma x xi ↔
      ¬ HasNegativeCycle (AuxTailMCFP0 tail head) (AuxHeadMCFP0 tail head)
        (AuxActiveMCFP0 cUpper cLower xi) (AuxLengthMCFP0 gamma) := by
  constructor
  · exact opt_no_negcycle tail head cUpper cLower gamma x xi
  · intro hno
    refine ⟨hfeas, fun xi' hf' => ?_⟩
    have hf'0 : FeasibleFlowMCFP0 tail head cUpper cLower gamma x xi' := hf'
    by_contra hlt
    rw [gam0 tail head cUpper cLower gamma x xi hfeas, gam0 tail head cUpper cLower gamma x xi' hf'0,
      WithTop.coe_le_coe] at hlt
    push_neg at hlt
    apply hno
    have hfe := (feas0_iff tail head cUpper cLower gamma x xi).1 hfeas
    have hfe' := (feas0_iff tail head cUpper cLower gamma x xi').1 hf'0
    have hfun : (fun b => xi' b - xi b) = fun b => xi' b + (-1) * xi b := by funext b; ring
    obtain ⟨k, c, hcR, hcyc, hneg⟩ := extract tail head gamma (AuxActiveMCFP0 cUpper cLower xi) _
      (fun b => xi' b - xi b) rfl
      (by
        funext v; rw [hfun, boundary_lin, hfe.2, hfe'.2]; simp)
      (by
        simp only [mul_sub, Finset.sum_sub_distrib]; linarith)
      (by
        intro e he
        cases e with
        | inl b =>
          have h : xi b < xi' b := by simp only [posArc] at he; linarith
          exact lt_of_lt_of_le (WithTop.coe_lt_coe.2 h) (hfe'.1 b).2
        | inr b =>
          have h : xi' b < xi b := by simp only [posArc] at he; linarith
          exact lt_of_le_of_lt (hfe'.1 b).1 (WithBot.coe_lt_coe.2 h))
    exact ⟨k, c, hcR, hcyc, by rw [cycleLength_eq]; exact_mod_cast hneg⟩

end NC

end DiscreteConvex.NetworkFlowsB

open DiscreteConvex.NetworkFlowsB
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

theorem solution (tail head : A → V) (cUpper : A → WithTop ℝ)
    (cLower : A → WithBot ℝ) (gamma : A → ℝ) (x : V → ℝ) (xi : A → ℝ)
    (hfeas : FeasibleFlowMCFP0 tail head cUpper cLower gamma x xi) :
    OptimalFlowMCFP0 tail head cUpper cLower gamma x xi ↔
      ¬ HasNegativeCycle (AuxTailMCFP0 tail head) (AuxHeadMCFP0 tail head)
        (AuxActiveMCFP0 cUpper cLower xi) (AuxLengthMCFP0 gamma) := by
  exact negative_cycle_criterion_mcfp0_core tail head cUpper cLower gamma x xi hfeas
