-- Prove2me | solution 1 for BeyondGomoryHu.Units.observation_5_3
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T04:25:59.09161+00:00
-- url     : https://prove2.me/submissions/980b96eb-1379-4484-9b62-daeee1b8bc79

import Mathlib
import Definitions.Def_BeyondGomoryHu_Units_Hierarchy

set_option autoImplicit false

namespace BeyondGomoryHu.Units

open Classical

private lemma obs53_isCut_mono {V : Type} [DecidableEq V]
    {S T A : Finset V} (hST : S ⊆ T) (hA : IsCut S A) : IsCut T A := by
  rcases hA with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  simp only [Finset.mem_inter] at ha
  simp only [Finset.mem_sdiff] at hb
  exact ⟨⟨a, Finset.mem_inter.mpr ⟨ha.1, hST ha.2⟩⟩,
    ⟨b, Finset.mem_sdiff.mpr ⟨hST hb.1, hb.2⟩⟩⟩

private lemma obs53_pair_subset {V : Type} [DecidableEq V]
    {S : Finset V} {a b : V} (ha : a ∈ S) (hb : b ∈ S) : ({a, b} : Finset V) ⊆ S := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact ha
  · exact hb

private lemma obs53_lam_le_cap {V : Type} [Fintype V] [DecidableEq V]
    (G : WGraph V) {S A : Finset V} (hA : IsCut S A) :
    lam G S ≤ (cap G A : ℕ∞) := by
  unfold lam
  exact iInf_le_of_le A (iInf_le_of_le hA le_rfl)

private lemma obs53_cap_le_lam {V : Type} [Fintype V] [DecidableEq V]
    (G : WGraph V) {S A : Finset V} (hA : IsMincut G S A) :
    (cap G A : ℕ∞) ≤ lam G S := by
  unfold lam
  refine le_iInf fun B => le_iInf fun hB => ?_
  exact_mod_cast hA.2 B hB

private lemma obs53_lam_eq_cap {V : Type} [Fintype V] [DecidableEq V]
    (G : WGraph V) {S A : Finset V} (hA : IsMincut G S A) :
    lam G S = (cap G A : ℕ∞) :=
  le_antisymm (obs53_lam_le_cap G hA.1) (obs53_cap_le_lam G hA)

private lemma obs53_lam_mono {V : Type} [Fintype V] [DecidableEq V]
    (G : WGraph V) {S T : Finset V} (hST : S ⊆ T) :
    lam G T ≤ lam G S := by
  unfold lam
  refine le_iInf fun A => le_iInf fun hA => ?_
  exact obs53_lam_le_cap G (obs53_isCut_mono hST hA)

private lemma obs53_exists_mincut {V : Type} [Fintype V] [DecidableEq V]
    (G : WGraph V) {S : Finset V} (h : ∃ A : Finset V, IsCut S A) :
    ∃ A : Finset V, IsMincut G S A := by
  classical
  let P : ℕ → Prop := fun k => ∃ A : Finset V, IsCut S A ∧ cap G A = k
  have hP : ∃ k, P k := by
    obtain ⟨A, hA⟩ := h
    exact ⟨cap G A, A, hA, rfl⟩
  obtain ⟨A, hA, hcap⟩ := Nat.find_spec hP
  refine ⟨A, hA, fun B hB => ?_⟩
  have hk : Nat.find hP ≤ cap G B := Nat.find_le ⟨B, hB, rfl⟩
  rwa [hcap]

private lemma obs53_lam_eq_top {V : Type} [Fintype V] [DecidableEq V]
    (G : WGraph V) {S : Finset V} (h : ∀ A : Finset V, ¬ IsCut S A) :
    lam G S = ⊤ := by
  apply top_unique
  unfold lam
  refine le_iInf fun A => le_iInf fun hA => ?_
  exact (h A hA).elim

private lemma obs53_sEquiv_refl {V : Type} [Fintype V] [DecidableEq V]
    (G : WGraph V) (S : Finset V) (a : V) : SEquiv G S a a :=
  fun _ _ => Iff.rfl

private lemma obs53_sEquiv_symm {V : Type} [Fintype V] [DecidableEq V]
    {G : WGraph V} {S : Finset V} {a b : V} (h : SEquiv G S a b) : SEquiv G S b a :=
  fun A hA => (h A hA).symm

private lemma obs53_sEquiv_trans {V : Type} [Fintype V] [DecidableEq V]
    {G : WGraph V} {S : Finset V} {a b c : V}
    (hab : SEquiv G S a b) (hbc : SEquiv G S b c) : SEquiv G S a c :=
  fun A hA => (hab A hA).trans (hbc A hA)

private lemma obs53_isCut_pair_of_separated {V : Type} [DecidableEq V]
    {a b : V} {A : Finset V}
    (h : (a ∈ A ∧ b ∉ A) ∨ (a ∉ A ∧ b ∈ A)) : IsCut {a, b} A := by
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact ⟨⟨a, by simp [ha]⟩, ⟨b, by simp [hb]⟩⟩
  · exact ⟨⟨b, by simp [hb]⟩, ⟨a, by simp [ha]⟩⟩

private lemma obs53_not_sEquiv_of_lca {V : Type} [Fintype V] [DecidableEq V]
    (G : WGraph V) {w z : V} {μ : Finset V} (hμ : IsLCA G w z μ)
    (hcut : ∃ A : Finset V, IsCut μ A) : ¬ SEquiv G μ w z := by
  classical
  intro hwz
  obtain ⟨A, hA⟩ := obs53_exists_mincut G hcut
  rcases hA.1 with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  simp only [Finset.mem_inter] at ha
  simp only [Finset.mem_sdiff] at hb
  have hab : a ≠ b := by
    intro hab
    subst b
    exact hb.2 ha.1
  have hcard : 2 ≤ μ.card := by
    have : 1 < μ.card := Finset.one_lt_card.mpr ⟨a, ha.2, b, hb.1, hab⟩
    omega
  have hnode : IsNode G (μ.filter (fun t => SEquiv G μ w t)) :=
    IsNode.child w hμ.1 hcard hμ.2.1
  have hwf : w ∈ μ.filter (fun t => SEquiv G μ w t) :=
    Finset.mem_filter.mpr ⟨hμ.2.1, obs53_sEquiv_refl G μ w⟩
  have hzf : z ∈ μ.filter (fun t => SEquiv G μ w t) :=
    Finset.mem_filter.mpr ⟨hμ.2.2.1, hwz⟩
  have hsub : μ ⊆ μ.filter (fun t => SEquiv G μ w t) :=
    hμ.2.2.2 _ hnode hwf hzf
  have haeq : SEquiv G μ w a := (Finset.mem_filter.mp (hsub ha.2)).2
  have hbeq : SEquiv G μ w b := (Finset.mem_filter.mp (hsub hb.1)).2
  have habmem : a ∈ A ↔ b ∈ A := ((haeq A hA).symm.trans (hbeq A hA))
  exact hb.2 (habmem.mp ha.1)

private lemma obs53_lam_pair_eq {V : Type} [Fintype V] [DecidableEq V]
    (G : WGraph V) {w z : V} {μ : Finset V} (hμ : IsLCA G w z μ) :
    lam G {w, z} = lam G μ := by
  have hpair : ({w, z} : Finset V) ⊆ μ := obs53_pair_subset hμ.2.1 hμ.2.2.1
  apply le_antisymm ?_ (obs53_lam_mono G hpair)
  by_cases hcut : ∃ A : Finset V, IsCut μ A
  · have hne := obs53_not_sEquiv_of_lca G hμ hcut
    unfold SEquiv at hne
    push_neg at hne
    obtain ⟨A, hA, hsep⟩ := hne
    calc
      lam G {w, z} ≤ (cap G A : ℕ∞) :=
        obs53_lam_le_cap G (obs53_isCut_pair_of_separated hsep)
      _ = lam G μ := (obs53_lam_eq_cap G hA).symm
  · have hno : ∀ A : Finset V, ¬ IsCut μ A := by
      intro A hA
      exact hcut ⟨A, hA⟩
    have hnoPair : ∀ A : Finset V, ¬ IsCut {w, z} A := by
      intro A hA
      exact hno A (obs53_isCut_mono hpair hA)
    rw [obs53_lam_eq_top G hno, obs53_lam_eq_top G hnoPair]

private lemma obs53_lam_lt_child {V : Type} [Fintype V] [DecidableEq V]
    (G : WGraph V) {μ : Finset V} (hcard : 2 ≤ μ.card) {s : V} (hs : s ∈ μ) :
    lam G μ < lam G (μ.filter (fun t => SEquiv G μ s t)) := by
  classical
  let ν := μ.filter (fun t => SEquiv G μ s t)
  have hsub : ν ⊆ μ := Finset.filter_subset _ _
  have hle : lam G μ ≤ lam G ν := obs53_lam_mono G hsub
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hcard' : 1 < μ.card := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard'
  have hcut : IsCut μ {a} := by
    exact ⟨⟨a, by simp [ha]⟩, ⟨b, by simp [hb, Ne.symm hab]⟩⟩
  obtain ⟨A, hA⟩ := obs53_exists_mincut G ⟨{a}, hcut⟩
  by_cases hνcut : ∃ B : Finset V, IsCut ν B
  · obtain ⟨B, hB⟩ := obs53_exists_mincut G hνcut
    have hcap : cap G A = cap G B := by
      have hcoe : (cap G A : ℕ∞) = (cap G B : ℕ∞) :=
        (obs53_lam_eq_cap G hA).symm.trans (heq.trans (obs53_lam_eq_cap G hB))
      exact_mod_cast hcoe
    have hBμ : IsMincut G μ B := by
      refine ⟨obs53_isCut_mono hsub hB.1, fun C hC => ?_⟩
      rw [← hcap]
      exact hA.2 C hC
    rcases hB.1 with ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    simp only [Finset.mem_inter] at hx
    simp only [Finset.mem_sdiff] at hy
    have hxeq : SEquiv G μ s x := (Finset.mem_filter.mp hx.2).2
    have hyeq : SEquiv G μ s y := (Finset.mem_filter.mp hy.1).2
    have hxymem : x ∈ B ↔ y ∈ B := ((hxeq B hBμ).symm.trans (hyeq B hBμ))
    exact hy.2 (hxymem.mp hx.1)
  · have hno : ∀ B : Finset V, ¬ IsCut ν B := by
      intro B hB
      exact hνcut ⟨B, hB⟩
    have htop : lam G ν = ⊤ := obs53_lam_eq_top G hno
    have hfin : lam G μ < ⊤ := by
      rw [obs53_lam_eq_cap G hA]
      simp
    exact (ne_of_lt hfin) (heq.trans htop)

private lemma obs53_lam_lt_of_not_mem {V : Type} [Fintype V] [DecidableEq V]
    (G : WGraph V) : ∀ {μ : Finset V}, IsNode G μ →
      ∀ {v z : V}, z ∈ μ → v ∉ μ → lam G {v, z} < lam G μ := by
  classical
  intro μ hμ
  induction hμ with
  | root =>
      intro v z hz hv
      exact (hv (Finset.mem_univ v)).elim
  | @child μ s hμ hcard hs ih =>
      intro v z hz hv
      have hzμ : z ∈ μ := (Finset.mem_filter.mp hz).1
      have hzs : SEquiv G μ s z := (Finset.mem_filter.mp hz).2
      by_cases hvμ : v ∈ μ
      · have hvs : ¬ SEquiv G μ s v := by
          intro hsv
          exact hv (Finset.mem_filter.mpr ⟨hvμ, hsv⟩)
        have hvz : ¬ SEquiv G μ v z := by
          intro hvz
          exact hvs (obs53_sEquiv_trans hzs (obs53_sEquiv_symm hvz))
        unfold SEquiv at hvz
        push_neg at hvz
        obtain ⟨A, hA, hsep⟩ := hvz
        have hle : lam G {v, z} ≤ lam G μ := by
          calc
            lam G {v, z} ≤ (cap G A : ℕ∞) :=
              obs53_lam_le_cap G (obs53_isCut_pair_of_separated hsep)
            _ = lam G μ := (obs53_lam_eq_cap G hA).symm
        exact hle.trans_lt (obs53_lam_lt_child G hcard hs)
      · have hlt := ih hzμ hvμ
        have hle : lam G μ ≤ lam G (μ.filter (fun t => SEquiv G μ s t)) :=
          obs53_lam_mono G (Finset.filter_subset _ _)
        exact hlt.trans_le hle

end BeyondGomoryHu.Units

open BeyondGomoryHu.Units

theorem solution {V : Type} [Fintype V] [DecidableEq V] (G : WGraph V) (hG : G.Connected) (w z : V) (μ : Finset V)
    (hμ : IsLCA G w z μ) :
    (μ : Set V) = {v | lam G {w, z} ≤ lam G {v, z}} := by
  classical
  have hlam : lam G {w, z} = lam G μ := BeyondGomoryHu.Units.obs53_lam_pair_eq G hμ
  ext v
  simp only [Finset.mem_coe, Set.mem_setOf_eq]
  constructor
  · intro hv
    calc
      lam G {w, z} = lam G μ := hlam
      _ ≤ lam G {v, z} := BeyondGomoryHu.Units.obs53_lam_mono G
        (BeyondGomoryHu.Units.obs53_pair_subset hv hμ.2.2.1)
  · intro hv
    by_contra hvμ
    have hlt := BeyondGomoryHu.Units.obs53_lam_lt_of_not_mem G hμ.1 hμ.2.2.1 hvμ
    exact (not_lt_of_ge hv) (hlt.trans_eq hlam.symm)