-- Prove2me | solution 1 for FeasibleBasesHC.Structure.theorem_3_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T17:10:39.250112+00:00
-- url     : https://prove2.me/submissions/6dbd56c6-b957-437f-8f66-228bb1836738

import Mathlib
import Definitions.Def_FeasibleBasesHC_Structure_Setting
import Theorems.Thm_FeasibleBasesHC_Structure_theorem_3_2
import Theorems.Thm_FeasibleBasesHC_Structure_theorem_3_3

open FeasibleBasesHC.Structure

namespace HCThm34Aux

lemma prod_alt (a c : ℝ) : ∀ m : ℕ,
    (∏ k : Fin (2 * m), (if k.val % 2 = 0 then a else c)) = a ^ m * c ^ m := by
  intro m
  rw [Fin.prod_univ_eq_prod_range (fun k => if k % 2 = 0 then a else c) (2 * m)]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.prod_range_succ,
      Finset.prod_range_succ, ih]
    have h1 : (2 * m) % 2 = 0 := by omega
    have h2 : (2 * m + 1) % 2 = 1 := by omega
    simp only [h1, h2, if_true, show (1 : ℕ) ≠ 0 by decide, if_false]
    ring

/-- Two "matchings" given by functions `σ` (bijective) and `f` (injective), whose arcs all lie in
a set `B` of arcs of `G'` containing no breakeven cycle, must coincide: otherwise the
alternating cycle in their union is a balanced cycle with multiplier one. -/
lemma key {n : ℕ} [NeZero n] (G : Digraph n) (beta : ℝ) (hbeta : 0 < beta)
    (B : Finset (GpArc n)) (hBarcs : B ⊆ (Gp G beta).arcs)
    (hgood : ∀ C : (Gp G beta).Cycle, (∀ i, C.edge i ∈ B) → C.multiplier ≠ 1)
    (σ : Equiv.Perm (Fin n)) (f : Fin n → Fin n) (hf : Function.Injective f)
    (hσB : ∀ i, (Sum.inl (i, σ i) : GpArc n) ∈ B)
    (hfB : ∀ i, (Sum.inl (i, f i) : GpArc n) ∈ B) :
    ∀ i, f i = σ i := by
  by_contra hne
  push Not at hne
  obtain ⟨i0, hi0⟩ := hne
  let π : Fin n → Fin n := fun i => σ.symm (f i)
  have hπinj : Function.Injective π := σ.symm.injective.comp hf
  have hσπ : ∀ i, σ (π i) = f i := fun i => by simp [π]
  -- π is a bijection of a finite type, so every point is periodic
  have hπbij : Function.Bijective π := hπinj.bijective_of_finite
  let πe : Equiv.Perm (Fin n) := Equiv.ofBijective π hπbij
  have hper : Function.IsPeriodicPt π (orderOf πe) i0 := by
    have h1 : (πe ^ orderOf πe) i0 = i0 := by rw [pow_orderOf_eq_one]; rfl
    rw [Equiv.Perm.coe_pow] at h1
    exact h1
  set m := Function.minimalPeriod π i0 with hmdef
  have hm : 0 < m := hper.minimalPeriod_pos (orderOf_pos πe)
  let it : ℕ → Fin n := fun t => π^[t] i0
  have hitm : it m = i0 := Function.iterate_minimalPeriod
  have hit_succ : ∀ t, it (t + 1) = π (it t) := fun t => Function.iterate_succ_apply' π t i0
  have hit_inj : ∀ a b, a < m → b < m → it a = it b → a = b := fun a b ha hb h =>
    Function.iterate_injOn_Iio_minimalPeriod ha hb h
  have hπ0 : π i0 ≠ i0 := by
    intro h
    apply hi0
    have := congrArg σ h
    rw [hσπ] at this
    exact this
  have hnofix : ∀ t, π (it t) ≠ it t := by
    intro t h
    apply hπ0
    have h2 : π^[t] (π i0) = π^[t] i0 := by
      rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
      exact h
    exact (hπinj.iterate t) h2
  have hfσ : ∀ t, f (it t) ≠ σ (it t) := by
    intro t h
    apply hnofix t
    apply σ.injective
    rw [hσπ]; exact h
  -- the alternating cycle of length 2m
  have hL : 0 < 2 * m := by omega
  let vtx : Fin (2 * m) → GpVertex n := fun k =>
    if k.val % 2 = 0 then Sum.inr (it (k.val / 2)) else Sum.inl (f (it (k.val / 2)))
  let edg : Fin (2 * m) → GpArc n := fun k =>
    if k.val % 2 = 0 then Sum.inl (it (k.val / 2), f (it (k.val / 2)))
    else Sum.inl (it (k.val / 2 + 1), σ (it (k.val / 2 + 1)))
  have hvtx_inj : Function.Injective vtx := by
    intro k k' h
    have hk := k.isLt
    have hk' := k'.isLt
    apply Fin.ext
    simp only [vtx] at h
    by_cases h1 : k.val % 2 = 0 <;> by_cases h2 : k'.val % 2 = 0 <;>
      simp only [h1, h2, if_true, if_false, reduceCtorEq, Sum.inl.injEq, Sum.inr.injEq] at h
    · have := hit_inj _ _ (by omega) (by omega) h; omega
    · have := hit_inj _ _ (by omega) (by omega) (hf h); omega
  have hedg_inj : Function.Injective edg := by
    intro k k' h
    have hk := k.isLt
    have hk' := k'.isLt
    apply Fin.ext
    simp only [edg] at h
    by_cases h1 : k.val % 2 = 0 <;> by_cases h2 : k'.val % 2 = 0 <;>
      simp only [h1, h2, if_true, if_false, Sum.inl.injEq, Prod.mk.injEq] at h
    · have := hit_inj _ _ (by omega) (by omega) h.1; omega
    · exfalso
      obtain ⟨ha, hb⟩ := h
      rw [ha] at hb
      exact hfσ _ hb
    · exfalso
      obtain ⟨ha, hb⟩ := h
      rw [← ha] at hb
      exact hfσ _ hb.symm
    · have ha := h.1
      rw [hit_succ, hit_succ] at ha
      have := hit_inj _ _ (by omega) (by omega) (hπinj ha); omega
  have hedgB : ∀ k, edg k ∈ B := by
    intro k
    simp only [edg]
    split_ifs
    · exact hfB _
    · exact hσB _
  let C : (Gp G beta).Cycle :=
    { length := 2 * m
      length_pos := hL
      vertex := vtx
      edge := edg
      forward := fun k => decide (k.val % 2 = 0)
      vertex_inj := hvtx_inj
      edge_inj := hedg_inj
      edge_mem := fun k => hBarcs (hedgB k)
      endpoints := by
        intro k
        have hk := k.isLt
        simp only
        by_cases h1 : k.val % 2 = 0
        · have hlt : k.val + 1 < 2 * m := by omega
          have hmod : (k.val + 1) % (2 * m) = k.val + 1 := Nat.mod_eq_of_lt hlt
          have h3 : (k.val + 1) % 2 ≠ 0 := by omega
          have h4 : (k.val + 1) / 2 = k.val / 2 := by omega
          simp only [h1, decide_true, if_true, edg, vtx, hmod, h3, if_false, h4]
          exact ⟨rfl, rfl⟩
        · simp only [h1, decide_false, Bool.false_eq_true, if_false, edg, vtx]
          refine ⟨?_, ?_⟩
          · show Sum.inl (σ (it (k.val / 2 + 1))) = Sum.inl (f (it (k.val / 2)))
            rw [hit_succ, hσπ]
          · by_cases hlt : k.val + 1 < 2 * m
            · have hmod : (k.val + 1) % (2 * m) = k.val + 1 := Nat.mod_eq_of_lt hlt
              have h3 : (k.val + 1) % 2 = 0 := by omega
              have h4 : (k.val + 1) / 2 = k.val / 2 + 1 := by omega
              simp only [hmod, h3, if_true, h4]
              rfl
            · have hmod : (k.val + 1) % (2 * m) = 0 := by
                rw [show k.val + 1 = 2 * m by omega, Nat.mod_self]
              have h4 : k.val / 2 + 1 = m := by omega
              simp only [hmod, Nat.zero_mod, if_true, Nat.zero_div]
              rw [h4, hitm]
              rfl }
  apply hgood C hedgB
  have hmu : ∀ k, (Gp G beta).mu (C.edge k) = beta := by
    intro k
    show (Gp G beta).mu (edg k) = beta
    simp only [edg]
    split_ifs <;> rfl
  unfold GNF.Cycle.multiplier
  simp only [hmu]
  have hnum : (∏ i : Fin C.length, if C.forward i then beta else 1) = beta ^ m * 1 ^ m := by
    rw [← prod_alt beta 1 m]
    apply Finset.prod_congr rfl
    intro k _
    simp [C]
  have hden : (∏ i : Fin C.length, if C.forward i then 1 else beta) = 1 ^ m * beta ^ m := by
    rw [← prod_alt 1 beta m]
    apply Finset.prod_congr rfl
    intro k _
    simp [C]
  rw [hnum, hden]
  have : beta ^ m ≠ 0 := pow_ne_zero _ hbeta.ne'
  field_simp

end HCThm34Aux

theorem solution {n : ℕ} [NeZero n] (G : Digraph n)
    (b : Basis n) (hb : b ∈ GamUlt G) :
    ∀ beta : ℝ, 0 < beta → beta < 1 →
      (Gp G beta).IsGoodAugTree (Bp b) ∧
      (Gp G beta).IsPerfectMatching ((thickArcs G b).image Sum.inl) ∧
      (∀ M : Finset (GpArc n), M ⊆ b.A.image Sum.inl →
        (Gp G beta).IsPerfectMatching M → M = (thickArcs G b).image Sum.inl) := by
  intro beta hb0 hb1
  have hT := theorem_3_2 G b hb beta hb0 hb1
  obtain ⟨_, ⟨σ, hσ⟩, _⟩ := theorem_3_3 G b hb
  have hBarcs : Bp b ⊆ (Gp G beta).arcs := hT.1.1
  have hthickA : thickArcs G b ⊆ b.A := by
    classical
    intro e he
    unfold thickArcs at he
    exact (Finset.mem_filter.mp he).1
  have hσB : ∀ i, (Sum.inl (i, σ i) : GpArc n) ∈ Bp b := by
    intro i
    have : (i, σ i) ∈ b.A := hthickA (by rw [hσ]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i))
    unfold Bp Basis.vars
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ this)
  have hAB : ∀ e ∈ b.A, (Sum.inl e : GpArc n) ∈ Bp b := by
    intro e he
    unfold Bp Basis.vars
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ he)
  have hthickPM : (Gp G beta).IsPerfectMatching ((thickArcs G b).image Sum.inl) := by
    refine ⟨?_, ?_⟩
    · intro a ha
      rw [hσ, Finset.image_image] at ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      exact hBarcs (hσB i)
    · intro v
      rcases v with j | j
      · refine ⟨Sum.inl (σ.symm j, j), ⟨?_, ?_⟩, ?_⟩
        · rw [hσ, Finset.image_image]
          exact Finset.mem_image.mpr ⟨σ.symm j, Finset.mem_univ _, by simp⟩
        · right; rfl
        · rintro a ⟨ha, hv⟩
          rw [hσ, Finset.image_image] at ha
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
          rcases hv with hv | hv
          · cases hv
          · simp only [Function.comp, Gp, Sum.inl.injEq] at hv
            subst hv
            simp
      · refine ⟨Sum.inl (j, σ j), ⟨?_, ?_⟩, ?_⟩
        · rw [hσ, Finset.image_image]
          exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
        · left; rfl
        · rintro a ⟨ha, hv⟩
          rw [hσ, Finset.image_image] at ha
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
          rcases hv with hv | hv
          · simp only [Function.comp, Gp, Sum.inr.injEq] at hv
            subst hv
            rfl
          · cases hv
  refine ⟨hT, hthickPM, ?_⟩
  intro M hMA hM
  -- every arc of M is an original arc
  have hMinl : ∀ a ∈ M, ∃ e ∈ b.A, a = Sum.inl e := by
    intro a ha
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp (hMA ha)
    exact ⟨e, he, rfl⟩
  -- the function f: the unique M-arc leaving w_i
  have hex : ∀ i : Fin n, ∃ j : Fin n, (Sum.inl (i, j) : GpArc n) ∈ M := by
    intro i
    obtain ⟨a, ⟨ha, hv⟩, _⟩ := hM.2 (Sum.inr i)
    obtain ⟨e, _, rfl⟩ := hMinl a ha
    rcases hv with hv | hv
    · simp only [Gp, Sum.inr.injEq] at hv
      obtain ⟨e1, e2⟩ := e
      simp only at hv
      subst hv
      exact ⟨e2, ha⟩
    · cases hv
  choose f hfM using hex
  have hfinj : Function.Injective f := by
    intro i i' h
    obtain ⟨a, _, hu⟩ := hM.2 (Sum.inl (f i))
    have e1 := hu (Sum.inl (i, f i)) ⟨hfM i, Or.inr rfl⟩
    have e2 := hu (Sum.inl (i', f i')) ⟨hfM i', Or.inr (by rw [h]; rfl)⟩
    have := e1.trans e2.symm
    simp only [Sum.inl.injEq, Prod.mk.injEq] at this
    exact this.1
  have hfB : ∀ i, (Sum.inl (i, f i) : GpArc n) ∈ Bp b := by
    intro i
    obtain ⟨e, he, hee⟩ := hMinl _ (hfM i)
    rw [hee]; exact hAB e he
  have hfσ := HCThm34Aux.key G beta hb0 (Bp b) hBarcs hT.1.2.2 σ f hfinj hσB hfB
  -- M consists exactly of the arcs (i, f i)
  have hMdesc : ∀ a, a ∈ M ↔ ∃ i, a = Sum.inl (i, f i) := by
    intro a
    constructor
    · intro ha
      obtain ⟨⟨i, j⟩, _, rfl⟩ := hMinl a ha
      obtain ⟨c, _, hu⟩ := hM.2 (Sum.inr i)
      have e1 := hu (Sum.inl (i, j)) ⟨ha, Or.inl rfl⟩
      have e2 := hu (Sum.inl (i, f i)) ⟨hfM i, Or.inl rfl⟩
      exact ⟨i, e1.trans e2.symm⟩
    · rintro ⟨i, rfl⟩; exact hfM i
  ext a
  rw [hMdesc, hσ, Finset.image_image]
  constructor
  · rintro ⟨i, rfl⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, by simp [hfσ i]⟩
  · intro ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact ⟨i, by simp [hfσ i]⟩
