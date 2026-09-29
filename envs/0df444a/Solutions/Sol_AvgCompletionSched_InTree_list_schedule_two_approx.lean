-- Prove2me | solution 1 for AvgCompletionSched.InTree.list_schedule_two_approx
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T20:59:36.643578+00:00
-- url     : https://prove2.me/submissions/fc4d9895-6338-4fe4-bc9a-b13c0c4edb07

import Mathlib
import Definitions.Def_AvgCompletionSched_InTree_Model
import Definitions.Def_AvgCompletionSched_InTree_ListScheduling

open MeasureTheory

namespace AvgCompletionSched.InTree

variable {n : ℕ}

lemma tg_functional {α : Type*} {f : α → Option α} {x u u' : α}
    (h1 : Relation.TransGen (fun a b => f a = some b) x u)
    (h2 : Relation.TransGen (fun a b => f a = some b) x u') :
    u = u' ∨ Relation.TransGen (fun a b => f a = some b) u u' ∨
      Relation.TransGen (fun a b => f a = some b) u' u := by
  induction h1 using Relation.TransGen.head_induction_on generalizing u' with
  | single h =>
    rcases Relation.TransGen.head'_iff.1 h2 with ⟨c, hc, hc'⟩
    rw [h] at hc
    cases Option.some_inj.1 hc
    rcases Relation.ReflTransGen.cases_head_iff.1 hc' with h' | ⟨d, hd, hd'⟩
    · left; exact h'
    · right; left; exact Relation.TransGen.head' hd hd'
  | head hac hcu ih =>
    rcases Relation.TransGen.head'_iff.1 h2 with ⟨c', hc, hc'⟩
    rw [hac] at hc
    cases Option.some_inj.1 hc
    rcases Relation.ReflTransGen.cases_head_iff.1 hc' with h' | ⟨d, hd, hd'⟩
    · subst h'; right; right; exact hcu
    · exact ih (Relation.TransGen.head' hd hd')

lemma key {I : Instance n} {m : ℕ} {π : Fin n ≃ Fin n} (hπ : ObeysPrecedence I π)
    {G : Schedule I m} (hG : IsListSchedule I π G) (j k : Fin n)
    (hk : π.symm j < π.symm k) (N : ℕ) :
    ∀ (t : ℝ) (i : Fin n), (Finset.univ.filter (fun y => G.C y < t)).card = N →
      π.symm i ≤ π.symm j → IsReady G i t → t < G.S i → G.S k ≤ t → t < G.C k → False := by
  classical
  induction N using Nat.strong_induction_on with
  | _ N IH =>
  intro t i hN hiB hir hti hkt htk
  have hC : ∀ y, G.S y < G.C y := fun y => by unfold Schedule.C; linarith [I.p_pos y]
  have notready : ∀ u, π.symm u ≤ π.symm j → G.S k < G.S u → ¬ IsReady G u (G.S k) := by
    intro u hu h1 h2
    have := hG.2 k u h1 h2
    exact absurd (lt_of_le_of_lt hu hk) (not_lt.2 this.le)
  have hkt' : G.S k < t := by
    rcases lt_or_eq_of_le hkt with h | h
    · exact h
    · exfalso
      exact notready i hiB (h ▸ hti) (h ▸ hir)
  have ht0 : 0 ≤ t := (G.nonneg k).trans hkt
  have hbusy : AllBusy G t := hG.1 i t ht0 hti hir
  set U := Finset.univ.filter (fun u => π.symm u ≤ π.symm j ∧ IsReady G u t ∧ t ≤ G.S u)
    with hU
  by_cases hA : ∃ u ∈ U, ∀ x, I.prec x u → G.C x < t
  · obtain ⟨u, huU, hu⟩ := hA
    simp only [hU, Finset.mem_filter, Finset.mem_univ, true_and] at huU
    obtain ⟨huB, hur, hut⟩ := huU
    have hnr := notready u huB (lt_of_lt_of_le hkt' hut)
    have hex : ∃ x, I.prec x u ∧ G.S k < G.C x := by
      by_contra hcon
      push_neg at hcon
      exact hnr hcon
    obtain ⟨x0, hx0, hx0C⟩ := hex
    have hmem : ∀ x, I.prec x u → x ∈ I.preds u := fun x hx => by
      simp [Instance.preds, hx]
    have hne : (I.preds u).Nonempty := ⟨x0, hmem x0 hx0⟩
    obtain ⟨x1, hx1, hx1e⟩ := Finset.exists_mem_eq_sup' hne G.C
    have hx1p : I.prec x1 u := by simpa [Instance.preds] using hx1
    have hs't : (I.preds u).sup' hne G.C < t := by rw [hx1e]; exact hu x1 hx1p
    have hks' : G.S k < (I.preds u).sup' hne G.C :=
      lt_of_lt_of_le hx0C (Finset.le_sup' G.C (hmem x0 hx0))
    have hur' : IsReady G u ((I.preds u).sup' hne G.C) :=
      fun x hx => Finset.le_sup' G.C (hmem x hx)
    have hlt : (Finset.univ.filter (fun y => G.C y < (I.preds u).sup' hne G.C)).card < N := by
      rw [← hN]
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨x1, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rw [← hx1e]; exact hs't
        · simp [hx1e]
      · intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
        linarith
    exact IH _ hlt _ u rfl huB hur' (by linarith) hks'.le (by linarith)
  · push_neg at hA
    set F := Finset.univ.filter (fun x => G.C x = t) with hF
    set Q := Finset.univ.filter (fun q => G.S q = t) with hQ
    have h1 : U.card ≤ F.card := by
      apply Finset.card_le_card_of_forall_subsingleton (fun u x => I.prec x u)
      · intro u hu
        obtain ⟨x, hx, hxt⟩ := hA u hu
        refine ⟨x, ?_, hx⟩
        simp only [hU, Finset.mem_filter, Finset.mem_univ, true_and] at hu
        simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and]
        exact le_antisymm (hu.2.1 x hx) hxt
      · intro x _ u1 hu1 u2 hu2
        obtain ⟨hu1U, hu1p⟩ := hu1
        obtain ⟨hu2U, hu2p⟩ := hu2
        simp only [Finset.mem_coe, hU, Finset.mem_filter, Finset.mem_univ, true_and] at hu1U hu2U
        rcases tg_functional hu1p hu2p with h | h | h
        · exact h
        · exfalso
          have := hu2U.2.1 u1 h
          linarith [hC u1, hu1U.2.2]
        · exfalso
          have := hu1U.2.1 u2 h
          linarith [hC u2, hu2U.2.2]
    have h2 : F.card ≤ Q.card := by
      apply Finset.card_le_card_of_forall_subsingleton (fun x q => G.M q = G.M x ∧ G.S q = t)
      · intro x hx
        simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        obtain ⟨q, hqM, hqS, hqC⟩ := hbusy (G.M x)
        have hqx : x ≠ q := by rintro rfl; linarith
        refine ⟨q, ?_, hqM, ?_⟩
        · simp only [hQ, Finset.mem_filter, Finset.mem_univ, true_and]
          rcases G.noOverlap x q hqM.symm hqx with h | h
          · have : G.C x ≤ G.S q := h
            linarith
          · have : G.C q ≤ G.S x := h
            linarith [hC x]
        · rcases G.noOverlap x q hqM.symm hqx with h | h
          · have : G.C x ≤ G.S q := h
            linarith
          · have : G.C q ≤ G.S x := h
            linarith [hC x]
      · intro q _ x1 hx1 x2 hx2
        obtain ⟨hx1U, hx1p⟩ := hx1
        obtain ⟨hx2U, hx2p⟩ := hx2
        simp only [Finset.mem_coe, hF, Finset.mem_filter, Finset.mem_univ, true_and] at hx1U hx2U
        by_contra hne
        rcases G.noOverlap x1 x2 (hx1p.1.symm.trans hx2p.1) hne with h | h
        · have : G.C x1 ≤ G.S x2 := h
          linarith [hC x2]
        · have : G.C x2 ≤ G.S x1 := h
          linarith [hC x1]
    have h3 : Q.card + 1 ≤ U.card := by
      have hsub : insert i Q ⊆ U := by
        intro q hq
        rw [Finset.mem_insert] at hq
        simp only [hU, Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hq with rfl | hq
        · exact ⟨hiB, hir, hti.le⟩
        · simp only [hQ, Finset.mem_filter, Finset.mem_univ, true_and] at hq
          refine ⟨?_, ?_, hq.ge⟩
          · have := hG.2 q i (hq ▸ hti) (hq ▸ hir)
            exact this.le.trans hiB
          · intro x hx
            have := G.precedence x q hx
            unfold Schedule.C; linarith
      have hiQ : i ∉ Q := by
        simp only [hQ, Finset.mem_filter, Finset.mem_univ, true_and]; exact hti.ne'
      rw [← Finset.card_insert_of_notMem hiQ]; exact Finset.card_le_card hsub
    omega

lemma kappa_unfold (I : Instance n) (i : Fin n) :
    kappa I i = if h : (I.preds i).Nonempty then
      I.p i + (I.preds i).attach.sup' (Finset.attach_nonempty_iff.mpr h) (fun x => kappa I x.1)
    else I.p i := by
  unfold kappa
  rw [WellFounded.fix_eq]

lemma kappa_empty (I : Instance n) (i : Fin n) (h : ¬ (I.preds i).Nonempty) :
    kappa I i = I.p i := by
  rw [kappa_unfold, dif_neg h]

lemma kappa_pred (I : Instance n) {x i : Fin n} (hx : I.prec x i) :
    I.p i + kappa I x ≤ kappa I i := by
  have hmem : x ∈ I.preds i := by simp [Instance.preds, hx]
  have h : (I.preds i).Nonempty := ⟨x, hmem⟩
  rw [kappa_unfold I i, dif_pos h]
  have := Finset.le_sup' (s := (I.preds i).attach) (fun x => kappa I x.1)
    (Finset.mem_attach _ ⟨x, hmem⟩)
  linarith

lemma kappa_le_C (I : Instance n) {m : ℕ} (N : Schedule I m) (i : Fin n) :
    kappa I i ≤ N.C i := by
  induction i using I.prec_wf.induction with
  | _ i IH =>
  by_cases h : (I.preds i).Nonempty
  · rw [kappa_unfold I i, dif_pos h]
    have : (I.preds i).attach.sup' (Finset.attach_nonempty_iff.mpr h) (fun x => kappa I x.1)
        ≤ N.S i := by
      apply Finset.sup'_le
      intro x _
      have hx : I.prec x.1 i := by simpa [Instance.preds] using x.2
      have := IH x.1 hx
      have h2 := N.precedence x.1 i hx
      unfold Schedule.C at this
      linarith
    unfold Schedule.C; linarith
  · rw [kappa_empty I i h]; unfold Schedule.C; linarith [N.nonneg i]

/-- busy set for B_j -/
def busyB {I : Instance n} {m : ℕ} (π : Fin n ≃ Fin n) (G : Schedule I m) (j : Fin n) : Set ℝ :=
  {t | ∀ μ : Fin m, ∃ b, π.symm b ≤ π.symm j ∧ G.M b = μ ∧ G.S b ≤ t ∧ t < G.C b}

lemma ready_busy {I : Instance n} {m : ℕ} {π : Fin n ≃ Fin n} (hπ : ObeysPrecedence I π)
    {G : Schedule I m} (hG : IsListSchedule I π G) (j i : Fin n) (hi : π.symm i ≤ π.symm j)
    (t : ℝ) (ht0 : 0 ≤ t) (hti : t < G.S i) (hr : IsReady G i t) : t ∈ busyB π G j := by
  classical
  intro μ
  obtain ⟨k, hkM, hkS, hkC⟩ := hG.1 i t ht0 hti hr μ
  refine ⟨k, ?_, hkM, hkS, hkC⟩
  by_contra hk
  rw [not_le] at hk
  exact key hπ hG j k hk _ t i rfl hi hr hti hkS hkC

lemma claim {I : Instance n} {m : ℕ} {π : Fin n ≃ Fin n} (hπ : ObeysPrecedence I π)
    {G : Schedule I m} (hG : IsListSchedule I π G) (j : Fin n) (i : Fin n) :
    π.symm i ≤ π.symm j →
    G.S i ≤ kappa I i - I.p i + volume.real (busyB π G j ∩ Set.Ico 0 (G.S i)) := by
  induction i using I.prec_wf.induction with
  | _ i IH =>
  intro hi
  have hC : ∀ y, G.S y < G.C y := fun y => by unfold Schedule.C; linarith [I.p_pos y]
  by_cases h : (I.preds i).Nonempty
  · obtain ⟨x, hx, hxe⟩ := Finset.exists_mem_eq_sup' h G.C
    have hxp : I.prec x i := by simpa [Instance.preds] using hx
    have hmem : ∀ y, I.prec y i → y ∈ I.preds i := fun y hy => by simp [Instance.preds, hy]
    have hxB : π.symm x ≤ π.symm j := ((hπ x i hxp).trans_le hi).le
    have ih := IH x hxp hxB
    have hk := kappa_pred I hxp
    have hprec := G.precedence x i hxp
    have hCx : G.C x ≤ G.S i := hprec
    have hsub1 : Set.Ico (G.C x) (G.S i) ⊆ busyB π G j := by
      intro t ht
      apply ready_busy hπ hG j i hi t ((G.nonneg x).trans (hC x).le |>.trans ht.1) ht.2
      intro y hy
      have := Finset.le_sup' G.C (hmem y hy)
      rw [hxe] at this
      linarith [ht.1]
    have hsub : (busyB π G j ∩ Set.Ico 0 (G.S x)) ∪ Set.Ico (G.C x) (G.S i) ⊆
        busyB π G j ∩ Set.Ico 0 (G.S i) := by
      intro t ht
      rcases ht with ht | ht
      · exact ⟨ht.1, ht.2.1, by linarith [ht.2.2, hC x]⟩
      · exact ⟨hsub1 ht, by linarith [ht.1, G.nonneg x, hC x], ht.2⟩
    have hdisj : Disjoint (busyB π G j ∩ Set.Ico 0 (G.S x)) (Set.Ico (G.C x) (G.S i)) := by
      rw [Set.disjoint_left]
      intro t h1 h2
      linarith [h1.2.2, h2.1, hC x]
    have hfin : volume (busyB π G j ∩ Set.Ico 0 (G.S i)) ≠ ⊤ :=
      measure_ne_top_of_subset Set.inter_subset_right (by simp)
    have hmono := measureReal_mono hsub hfin
    rw [measureReal_union hdisj measurableSet_Ico
      (measure_ne_top_of_subset Set.inter_subset_right (by simp)) (by simp),
      Real.volume_real_Ico_of_le hCx] at hmono
    have hCe : G.C x = G.S x + I.p x := rfl
    linarith
  · rw [kappa_empty I i h]
    have hsub : Set.Ico 0 (G.S i) ⊆ busyB π G j ∩ Set.Ico 0 (G.S i) := by
      intro t ht
      refine ⟨ready_busy hπ hG j i hi t ht.1 ht.2 ?_, ht⟩
      intro y hy
      exact absurd ⟨y, by simp [Instance.preds, hy]⟩ h
    have hfin : volume (busyB π G j ∩ Set.Ico 0 (G.S i)) ≠ ⊤ :=
      measure_ne_top_of_subset Set.inter_subset_right (by simp)
    have := measureReal_mono hsub hfin
    rw [Real.volume_real_Ico_of_le (G.nonneg i)] at this
    linarith

lemma busy_bound {I : Instance n} {m : ℕ} (π : Fin n ≃ Fin n) (G : Schedule I m) (j : Fin n)
    (s : ℝ) :
    (m : ℝ) * volume.real (busyB π G j ∩ Set.Ico 0 s) ≤ oneMachineC I π j := by
  classical
  have hre : oneMachineC I π j =
      ∑ k ∈ Finset.univ.filter (fun k => π.symm k ≤ π.symm j), I.p k := by
    unfold oneMachineC
    apply Finset.sum_equiv π
    · intro i; simp
    · intro i _; rfl
  rw [hre, ← Finset.sum_fiberwise (Finset.univ.filter (fun k => π.symm k ≤ π.symm j)) G.M]
  have hmach : ∀ μ : Fin m, volume.real (busyB π G j ∩ Set.Ico 0 s) ≤
      ∑ k ∈ (Finset.univ.filter (fun k => π.symm k ≤ π.symm j)).filter (fun k => G.M k = μ),
        I.p k := by
    intro μ
    set T := (Finset.univ.filter (fun k => π.symm k ≤ π.symm j)).filter (fun k => G.M k = μ)
    have hsub : busyB π G j ∩ Set.Ico 0 s ⊆ ⋃ k ∈ T, Set.Ico (G.S k) (G.C k) := by
      intro t ht
      obtain ⟨b, hb, hbM, hbS, hbC⟩ := ht.1 μ
      simp only [Set.mem_iUnion]
      exact ⟨b, by simp [T, hb, hbM], hbS, hbC⟩
    have h1 := measureReal_mono (μ := volume) hsub
      ((measure_biUnion_finset_le T (fun k => Set.Ico (G.S k) (G.C k))).trans_lt
        (ENNReal.sum_lt_top.2 (fun k _ => by simp))).ne
    refine h1.trans ((measureReal_biUnion_finset_le T _).trans (le_of_eq ?_))
    apply Finset.sum_congr rfl
    intro k _
    rw [Real.volume_real_Ico_of_le (by unfold Schedule.C; linarith [I.p_pos k])]
    unfold Schedule.C; ring
  calc (m : ℝ) * volume.real (busyB π G j ∩ Set.Ico 0 s)
      = ∑ _μ : Fin m, volume.real (busyB π G j ∩ Set.Ico 0 s) := by simp
    _ ≤ _ := Finset.sum_le_sum (fun μ _ => hmach μ)

theorem completion_bound_core {n : ℕ} (I : Instance n) (m : ℕ) (hm : 1 ≤ m)
    (π : Fin n ≃ Fin n) (hπ : ObeysPrecedence I π) (G : Schedule I m)
    (hG : IsListSchedule I π G) (i : Fin n) :
    G.C i ≤ kappa I i + oneMachineC I π i / (m : ℝ) := by
  have h1 := claim hπ hG i i le_rfl
  have h2 := busy_bound (I := I) π G i (G.S i)
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h3 : volume.real (busyB π G i ∩ Set.Ico 0 (G.S i)) ≤ oneMachineC I π i / m := by
    rw [le_div_iff₀ hm']; linarith
  unfold Schedule.C; linarith

/-- Packing bound: jobs completing by time `t` have total length at most `m t`. -/
lemma pack {I : Instance n} {m : ℕ} (N : Schedule I m) (t : ℝ) (ht : 0 ≤ t) :
    ∑ k ∈ Finset.univ.filter (fun k => N.C k ≤ t), I.p k ≤ m * t := by
  rw [← Finset.sum_fiberwise (Finset.univ.filter (fun k => N.C k ≤ t)) N.M]
  have hmach : ∀ μ : Fin m,
      ∑ k ∈ (Finset.univ.filter (fun k => N.C k ≤ t)).filter (fun k => N.M k = μ), I.p k ≤ t := by
    intro μ
    set T := (Finset.univ.filter (fun k => N.C k ≤ t)).filter (fun k => N.M k = μ) with hT
    have hdisj : Set.PairwiseDisjoint (↑T) (fun k => Set.Ico (N.S k) (N.S k + I.p k)) := by
      intro a ha b hb hab
      simp only [hT, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha hb
      rw [Function.onFun, Set.disjoint_left]
      intro x hxa hxb
      rcases N.noOverlap a b (ha.2.trans hb.2.symm) hab with h | h
      · linarith [hxa.2, hxb.1]
      · linarith [hxa.1, hxb.2]
    have hsub : (⋃ k ∈ T, Set.Ico (N.S k) (N.S k + I.p k)) ⊆ Set.Icc 0 t := by
      intro x hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨k, hk, hx⟩ := hx
      simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      have h1 := N.nonneg k
      have h2 : N.S k + I.p k ≤ t := hk.1
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hvol := measure_mono (μ := (volume : Measure ℝ)) hsub
    rw [measure_biUnion_finset hdisj (fun k _ => measurableSet_Ico)] at hvol
    simp only [Real.volume_Ico, Real.volume_Icc, add_sub_cancel_left, sub_zero] at hvol
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => (I.p_pos k).le)] at hvol
    exact (ENNReal.ofReal_le_ofReal_iff ht).1 hvol
  calc ∑ μ : Fin m, ∑ k ∈ (Finset.univ.filter (fun k => N.C k ≤ t)).filter
          (fun k => N.M k = μ), I.p k
      ≤ ∑ _μ : Fin m, t := Finset.sum_le_sum (fun μ _ => hmach μ)
    _ = m * t := by simp

/-- Strict "earlier" relation: by completion time, ties broken by index. -/
def before {I : Instance n} {m : ℕ} (N : Schedule I m) (k j : Fin n) : Prop :=
  N.C k < N.C j ∨ (N.C k = N.C j ∧ k < j)

lemma before_trans {I : Instance n} {m : ℕ} (N : Schedule I m) {a b c : Fin n}
    (h1 : before N a b) (h2 : before N b c) : before N a c := by
  unfold before at *
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · left; linarith
  · left; linarith
  · left; linarith
  · right; exact ⟨h1.trans h2, h1'.trans h2'⟩

lemma before_irrefl {I : Instance n} {m : ℕ} (N : Schedule I m) (a : Fin n) :
    ¬ before N a a := by
  unfold before; rintro (h | ⟨_, h⟩) <;> exact lt_irrefl _ h

lemma before_total {I : Instance n} {m : ℕ} (N : Schedule I m) {a b : Fin n} (hab : a ≠ b) :
    before N a b ∨ before N b a := by
  unfold before
  rcases lt_trichotomy (N.C a) (N.C b) with h | h | h
  · left; left; exact h
  · rcases lt_or_gt_of_ne hab with h' | h'
    · left; right; exact ⟨h, h'⟩
    · right; right; exact ⟨h.symm, h'⟩
  · right; left; exact h

open Classical in
noncomputable def rankN {I : Instance n} {m : ℕ} (N : Schedule I m) (j : Fin n) : ℕ :=
  (Finset.univ.filter (fun k => before N k j)).card

lemma rankN_lt {I : Instance n} {m : ℕ} (N : Schedule I m) (j : Fin n) : rankN N j < n := by
  classical
  unfold rankN
  have : (Finset.univ.filter (fun k => before N k j)) ⊂ Finset.univ := by
    refine Finset.ssubset_iff_subset_ne.2 ⟨Finset.subset_univ _, fun h => ?_⟩
    have hj : j ∈ Finset.univ.filter (fun k => before N k j) := by rw [h]; exact Finset.mem_univ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact before_irrefl N j hj
  have := Finset.card_lt_card this
  simpa using this

lemma rankN_strict {I : Instance n} {m : ℕ} (N : Schedule I m) {a b : Fin n}
    (h : before N a b) : rankN N a < rankN N b := by
  classical
  unfold rankN
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.2 ⟨?_, fun he => ?_⟩
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact before_trans N hk h
  · have ha : a ∈ Finset.univ.filter (fun k => before N k b) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h
    rw [← he] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    exact before_irrefl N a ha

noncomputable def rankF {I : Instance n} {m : ℕ} (N : Schedule I m) (j : Fin n) : Fin n :=
  ⟨rankN N j, rankN_lt N j⟩

lemma rankF_inj {I : Instance n} {m : ℕ} (N : Schedule I m) : Function.Injective (rankF N) := by
  intro a b h
  by_contra hab
  have h' : rankN N a = rankN N b := congrArg Fin.val h
  rcases before_total N hab with h1 | h1
  · exact absurd h' (rankN_strict N h1).ne
  · exact absurd h' (rankN_strict N h1).ne'

theorem one_machine_lb_core {n : ℕ} (I : Instance n) (m : ℕ) (hm : 1 ≤ m)
    (π : Fin n ≃ Fin n) (hπ : IsOptimalOneMachine I π) (N : Schedule I m) :
    oneMachineWct I π / (m : ℝ) ≤ N.wct := by
  have hbij : Function.Bijective (rankF N) :=
    (Finite.injective_iff_bijective).1 (rankF_inj N)
  set e := Equiv.ofBijective (rankF N) hbij with he
  set σ := e.symm with hσ
  have hσs : ∀ j, σ.symm j = rankF N j := by intro j; simp [hσ, he]
  -- σ obeys precedence
  have hobey : ObeysPrecedence I σ := by
    intro i j hij
    rw [hσs, hσs]
    have hp := I.p_pos i
    have hpj := I.p_pos j
    have h1 := N.precedence i j hij
    have hb : before N i j := by
      left; unfold Schedule.C; linarith
    exact rankN_strict N hb
  -- one-machine completion times are at most m * C_j
  have hC : ∀ j, oneMachineC I σ j ≤ m * N.C j := by
    intro j
    unfold oneMachineC
    have hre : ∑ k ∈ Finset.univ.filter (fun k => k ≤ σ.symm j), I.p (σ k) =
        ∑ k ∈ Finset.univ.filter (fun k => σ.symm k ≤ σ.symm j), I.p k := by
      apply Finset.sum_equiv σ
      · intro i; simp
      · intro i _; rfl
    rw [hre]
    have hsub : Finset.univ.filter (fun k => σ.symm k ≤ σ.symm j) ⊆
        Finset.univ.filter (fun k => N.C k ≤ N.C j) := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      by_contra hlt
      rw [not_le] at hlt
      have hb : before N j k := Or.inl hlt
      have := rankN_strict N hb
      rw [hσs, hσs] at hk
      exact absurd hk (not_le.2 this)
    have hCj : 0 ≤ N.C j := by
      unfold Schedule.C; linarith [N.nonneg j, I.p_pos j]
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun k _ _ => (I.p_pos k).le)).trans (pack N (N.C j) hCj)
  have hle : oneMachineWct I π ≤ oneMachineWct I σ := hπ.2 σ hobey
  have hσle : oneMachineWct I σ ≤ m * N.wct := by
    unfold oneMachineWct Schedule.wct
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have := mul_le_mul_of_nonneg_left (hC j) (I.w_pos j).le
    linarith
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [div_le_iff₀ hm']
  linarith


theorem two_approx_core {n : ℕ} (I : Instance n) (m : ℕ) (hm : 1 ≤ m)
    (π : Fin n ≃ Fin n) (hπ : IsOptimalOneMachine I π) (G : Schedule I m)
    (hG : IsListSchedule I π G) (N : Schedule I m) :
    G.wct ≤ 2 * N.wct := by
  have h1 := one_machine_lb_core I m hm π hπ N
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h2 : G.wct ≤ ∑ j, I.w j * kappa I j + oneMachineWct I π / m := by
    unfold Schedule.wct oneMachineWct
    rw [Finset.sum_div, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    have := completion_bound_core I m hm π hπ.1 G hG j
    have hw := (I.w_pos j).le
    rw [mul_div_assoc]
    nlinarith
  have h3 : ∑ j, I.w j * kappa I j ≤ N.wct := by
    unfold Schedule.wct
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left (kappa_le_C I N j) (I.w_pos j).le
  linarith

end AvgCompletionSched.InTree

open AvgCompletionSched.InTree


theorem solution {n : ℕ} (I : Instance n) (m : ℕ) (hm : 1 ≤ m)
    (π : Fin n ≃ Fin n) (hπ : IsOptimalOneMachine I π) (G : Schedule I m)
    (hG : IsListSchedule I π G) (N : Schedule I m) :
    G.wct ≤ 2 * N.wct := by
  exact two_approx_core I m hm π hπ G hG N
