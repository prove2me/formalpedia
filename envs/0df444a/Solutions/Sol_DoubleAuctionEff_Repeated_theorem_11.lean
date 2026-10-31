-- Prove2me | solution 1 for DoubleAuctionEff.Repeated.theorem_11
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T20:55:39.754637+00:00
-- url     : https://prove2.me/submissions/730c7f00-6362-463d-b0a8-bae0267c9495

import Mathlib
import Definitions.Def_DoubleAuctionEff_Repeated_Model

open DoubleAuctionEff.Repeated Filter Topology

namespace DAEThm11Aux

theorem u_ne_top {J : Type*} {u : (J → ℝ) → EReal} {g : J → ℝ} (h1 : Assumption1 u g)
    (x : J → ℝ) : u x ≠ ⊤ := by
  intro h
  have hx : x ∈ dom u := by simp [dom, h]
  have := h1.2.2 x hx 1 one_pos
  rw [h] at this
  exact not_top_lt this

theorem mono_g {J : Type*} {u : (J → ℝ) → EReal} {g : J → ℝ} (h1 : Assumption1 u g)
    (z : J → ℝ) {s : ℝ} (hs : 0 ≤ s) : u z ≤ u (z + s • g) := by
  rcases hs.lt_or_eq with hs | hs
  · by_cases hz : z ∈ dom u
    · exact (h1.2.2 z hz s hs).le
    · simp only [dom, Set.mem_setOf_eq, not_lt, le_bot_iff] at hz
      simp [hz]
  · subst hs; simp

theorem le_indiff {J : Type*} {u : (J → ℝ) → EReal} {g x0 y : J → ℝ} {r : ℝ}
    (h : u x0 ≤ u (x0 + y - r • g)) : (r : EReal) ≤ indiffPrice u g x0 y := by
  unfold indiffPrice
  exact le_iSup₂ (f := fun (r : ℝ) (_ : u x0 ≤ u (x0 + y - r • g)) => (r : EReal)) r h

theorem indiff_zero_nonneg {J : Type*} (u : (J → ℝ) → EReal) (g x0 : J → ℝ) :
    (0 : EReal) ≤ indiffPrice u g x0 0 := by
  have := le_indiff (u := u) (g := g) (x0 := x0) (y := 0) (r := 0) (by simp)
  simpa using this

theorem CS_nonneg {I J : Type*} [Fintype I] (u : I → (J → ℝ) → EReal) (g : J → ℝ)
    (x : I → J → ℝ) : 0 ≤ CS u g x := by
  unfold CS
  refine le_trans ?_ (le_iSup₂ (f := fun (y : I → J → ℝ) (_ : ∑ i, y i = 0) =>
    ∑ i, indiffPrice (u i) g (x i) (y i)) 0 (by simp))
  exact Finset.sum_nonneg fun i _ => by simpa using indiff_zero_nonneg (u i) g (x i)

theorem admissible_of_lt {J : Type*} {u : (J → ℝ) → EReal} {g x0 y : J → ℝ} {r : ℝ}
    (h1 : Assumption1 u g) (h : (r : EReal) < indiffPrice u g x0 y) :
    u x0 ≤ u (x0 + y - r • g) := by
  unfold indiffPrice at h
  obtain ⟨r', hr'⟩ := lt_iSup_iff.1 h
  obtain ⟨hadm, hlt⟩ := lt_iSup_iff.1 hr'
  rw [EReal.coe_lt_coe_iff] at hlt
  have := mono_g h1 (x0 + y - r' • g) (s := r' - r) (by linarith)
  refine hadm.trans (this.trans (le_of_eq ?_))
  congr 1; rw [sub_smul]; abel

theorem split2 (a b : EReal) (t : ℝ) (h : (t : EReal) < a + b) :
    ∃ t1 t2 : ℝ, (t1 : EReal) < a ∧ (t2 : EReal) < b ∧ t ≤ t1 + t2 := by
  induction a using EReal.rec with
  | bot => simp at h
  | top =>
    induction b using EReal.rec with
    | bot => simp at h
    | top => exact ⟨t, 0, EReal.coe_lt_top _, EReal.coe_lt_top _, by simp⟩
    | coe β => exact ⟨t - β + 1, β - 1, EReal.coe_lt_top _, by exact_mod_cast (by linarith),
        by linarith⟩
  | coe α =>
    induction b using EReal.rec with
    | bot => simp at h
    | top => exact ⟨α - 1, t - α + 1, by exact_mod_cast (by linarith), EReal.coe_lt_top _,
        by linarith⟩
    | coe β =>
      rw [← EReal.coe_add, EReal.coe_lt_coe_iff] at h
      refine ⟨α - (α + β - t) / 2, β - (α + β - t) / 2, ?_, ?_, by linarith⟩ <;>
        exact_mod_cast (by linarith)

theorem split_sum {I : Type*} [DecidableEq I] (f : I → EReal) (s : Finset I) :
    ∀ t : ℝ, (t : EReal) < ∑ i ∈ s, f i →
      ∃ c : I → ℝ, (∀ i ∈ s, (c i : EReal) < f i) ∧ t ≤ ∑ i ∈ s, c i := by
  induction s using Finset.induction_on with
  | empty =>
    intro t ht
    refine ⟨0, by simp, ?_⟩
    simp only [Finset.sum_empty] at ht ⊢
    exact_mod_cast ht.le
  | insert j s hj ih =>
    intro t ht
    rw [Finset.sum_insert hj] at ht
    obtain ⟨t1, t2, h1, h2, h12⟩ := split2 _ _ t ht
    obtain ⟨c, hc, hcs⟩ := ih t2 h2
    refine ⟨Function.update c j t1, ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · simpa using h1
      · have : i ≠ j := fun h => hj (h ▸ hi)
        simpa [Function.update_of_ne this] using hc i hi
    · rw [Finset.sum_insert hj, Function.update_self]
      have : ∑ i ∈ s, Function.update c j t1 i = ∑ i ∈ s, c i := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have : i ≠ j := fun h => hj (h ▸ hi)
        simp [Function.update_of_ne this]
      rw [this]; linarith

end DAEThm11Aux

open DAEThm11Aux in
theorem solution {I J : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J]
    [DecidableEq J] (u : I → (J → ℝ) → EReal) (g : J → ℝ) (h1 : ∀ i, Assumption1 (u i) g) :
    (∀ x : I → J → ℝ, (∀ i, x i ∈ dom (u i)) → IsParetoEfficient u x x →
        IsDAEquilibrium u g x) ∧
      ((∀ i, Assumption4 (u i) g) → ∀ x : I → J → ℝ, IsDAEquilibrium u g x →
        IsParetoEfficient u x x) := by
  constructor
  · -- Pareto allocations are equilibria
    intro x hdom hpar
    unfold IsDAEquilibrium
    refine le_antisymm ?_ (CS_nonneg u g x)
    by_contra hpos
    push_neg at hpos
    unfold CS at hpos
    obtain ⟨y, hy⟩ := lt_iSup_iff.1 hpos
    obtain ⟨hysum, hy⟩ := lt_iSup_iff.1 hy
    obtain ⟨t', ht'0, ht'⟩ := EReal.lt_iff_exists_real_btwn.1 hy
    have ht'0' : (0 : ℝ) < t' := by exact_mod_cast ht'0
    obtain ⟨c, hc, hcs⟩ := split_sum (fun i => indiffPrice (u i) g (x i) (y i)) Finset.univ t' ht'
    set R : ℝ := ∑ i, c i
    have hR : 0 < R := lt_of_lt_of_le ht'0' hcs
    set n : ℝ := (Fintype.card I : ℝ)
    have hn : 0 < n := by simp [n, Fintype.card_pos]
    set x' : I → J → ℝ := fun i => x i + y i - c i • g + (R / n) • g
    apply hpar.2
    refine ⟨x', ?_, ?_, ?_⟩
    · show ∑ i, x' i = ∑ i, x i
      simp only [x', Finset.sum_add_distrib, Finset.sum_sub_distrib, hysum, ← Finset.sum_smul]
      rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ, smul_eq_mul,
        show (Fintype.card I : ℝ) * (R / n) = R by simp only [n]; field_simp]
      simp [R]
    · have hstrict : ∀ i, u i (x i) < u i (x' i) := by
        intro i
        have hadm := admissible_of_lt (h1 i) (hc i (Finset.mem_univ i))
        have hd : x i + y i - c i • g ∈ dom (u i) := lt_of_lt_of_le (hdom i) hadm
        exact lt_of_le_of_lt hadm ((h1 i).2.2 _ hd _ (div_pos hR hn))
      intro i; exact (hstrict i).le
    · obtain ⟨i⟩ := (inferInstance : Nonempty I)
      refine ⟨i, ?_⟩
      have hadm := admissible_of_lt (h1 i) (hc i (Finset.mem_univ i))
      have hd : x i + y i - c i • g ∈ dom (u i) := lt_of_lt_of_le (hdom i) hadm
      exact lt_of_le_of_lt hadm ((h1 i).2.2 _ hd _ (div_pos hR hn))
  · -- equilibria are Pareto under Assumption 4
    intro h4 x heq
    refine ⟨rfl, ?_⟩
    rintro ⟨x', hfeas, hge, i0, hlt⟩
    -- every agent is in the domain: otherwise CS x = ⊤
    have hdom : ∀ i, x i ∈ dom (u i) := by
      intro i
      by_contra hni
      simp only [dom, Set.mem_setOf_eq, not_lt, le_bot_iff] at hni
      have htop : indiffPrice (u i) g (x i) 0 = ⊤ := by
        refine EReal.eq_top_iff_forall_lt _ |>.2 fun y => ?_
        exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (lt_add_one y))
          (le_indiff (by simp [hni]))
      have hCS : (⊤ : EReal) ≤ CS u g x := by
        unfold CS
        refine le_trans ?_ (le_iSup₂ (f := fun (y : I → J → ℝ) (_ : ∑ i, y i = 0) =>
          ∑ i, indiffPrice (u i) g (x i) (y i)) 0 (by simp))
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
        simp only [Pi.zero_apply]
        rw [htop]
        have : (0 : EReal) ≤ ∑ j ∈ Finset.univ.erase i, indiffPrice (u j) g (x j) 0 :=
          Finset.sum_nonneg fun j _ => indiff_zero_nonneg (u j) g (x j)
        rw [EReal.top_add_of_ne_bot (ne_bot_of_le_ne_bot (by simp) this)]
      unfold IsDAEquilibrium at heq
      rw [heq] at hCS
      exact absurd hCS (by simp)
    -- strictly better agent can give up some numeraire
    have hx'dom : x' i0 ∈ dom (u i0) := lt_trans (hdom i0) hlt
    have hev := h4 i0 (x' i0) (x i0) (hdom i0) hlt
    obtain ⟨ε0, hε0, hε0dom⟩ : ∃ ε0 : ℝ, 0 < ε0 ∧ x' i0 - ε0 • g ∈ dom (u i0) := by
      obtain ⟨ε0, hε0, h⟩ := (hev.and self_mem_nhdsWithin).exists
      exact ⟨ε0, h, hε0⟩
    -- real values
    set a : ℝ := (u i0 (x' i0)).toReal
    set b : ℝ := (u i0 (x' i0 - ε0 • g)).toReal
    set v : ℝ := (u i0 (x i0)).toReal
    have ha : u i0 (x' i0) = a := (EReal.coe_toReal (u_ne_top (h1 i0) _) (ne_of_gt hx'dom)).symm
    have hb : u i0 (x' i0 - ε0 • g) = b :=
      (EReal.coe_toReal (u_ne_top (h1 i0) _) (ne_of_gt hε0dom)).symm
    have hv : u i0 (x i0) = v := (EReal.coe_toReal (u_ne_top (h1 i0) _) (ne_of_gt (hdom i0))).symm
    have hva : v < a := by rw [ha, hv] at hlt; exact_mod_cast hlt
    -- choose θ small so that the concave combination still beats v
    have hcont : Tendsto (fun θ : ℝ => (1 - θ) * a + θ * b) (𝓝 0) (𝓝 ((1 - 0) * a + 0 * b)) :=
      ((tendsto_const_nhds.sub tendsto_id).mul tendsto_const_nhds).add
        (tendsto_id.mul tendsto_const_nhds)
    rw [sub_zero, one_mul, zero_mul, add_zero] at hcont
    have hev2 : ∀ᶠ θ in 𝓝[>] (0 : ℝ), v < (1 - θ) * a + θ * b ∧ θ < 1 :=
      ((hcont.eventually (lt_mem_nhds hva)).and (gt_mem_nhds one_pos)).filter_mono
        nhdsWithin_le_nhds
    obtain ⟨θ, ⟨hθv, hθ1⟩, hθ0⟩ := (hev2.and self_mem_nhdsWithin).exists
    have hθ0' : 0 < θ := hθ0
    have hA : ((x' i0, a) : (J → ℝ) × ℝ) ∈ {q : (J → ℝ) × ℝ | ((q.2 : ℝ) : EReal) ≤ u i0 q.1} := by
      show (a : EReal) ≤ _; rw [ha]
    have hB : ((x' i0 - ε0 • g, b) : (J → ℝ) × ℝ) ∈
        {q : (J → ℝ) × ℝ | ((q.2 : ℝ) : EReal) ≤ u i0 q.1} := by
      show (b : EReal) ≤ _; rw [hb]
    have hC := (h1 i0).2.1 hA hB (sub_nonneg.2 hθ1.le) hθ0'.le (by ring)
    have hpt : (1 - θ) • x' i0 + θ • (x' i0 - ε0 • g) = x' i0 - (θ * ε0) • g := by
      rw [smul_sub, smul_smul, sub_smul, one_smul]; abel
    have hC' : (((1 - θ) * a + θ * b : ℝ) : EReal) ≤ u i0 (x' i0 - (θ * ε0) • g) := by
      have := hC
      simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd,
        smul_eq_mul] at this
      rwa [hpt] at this
    set e : ℝ := θ * ε0
    have he : 0 < e := mul_pos hθ0' hε0
    -- the surplus at y = x' - x is at least e
    set y : I → J → ℝ := fun i => x' i - x i
    have hysum : ∑ i, y i = 0 := by
      simp only [y, Finset.sum_sub_distrib]; rw [hfeas]; simp
    have hDi0 : (e : EReal) ≤ indiffPrice (u i0) g (x i0) (y i0) := by
      apply le_indiff
      simp only [y, add_sub_cancel]
      rw [hv]; exact (EReal.coe_le_coe_iff.2 hθv.le).trans hC'
    have hDi : ∀ i, (0 : EReal) ≤ indiffPrice (u i) g (x i) (y i) := by
      intro i
      have := le_indiff (u := u i) (g := g) (x0 := x i) (y := y i) (r := 0)
        (by simp only [y, add_sub_cancel, zero_smul, sub_zero]; exact hge i)
      simpa using this
    have hsum : (e : EReal) ≤ ∑ i, indiffPrice (u i) g (x i) (y i) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0)]
      have : (0 : EReal) ≤ ∑ j ∈ Finset.univ.erase i0, indiffPrice (u j) g (x j) (y j) :=
        Finset.sum_nonneg fun j _ => hDi j
      simpa using add_le_add hDi0 this
    have hCS : (e : EReal) ≤ CS u g x := by
      unfold CS
      exact hsum.trans (le_iSup₂ (f := fun (y : I → J → ℝ) (_ : ∑ i, y i = 0) =>
        ∑ i, indiffPrice (u i) g (x i) (y i)) y hysum)
    unfold IsDAEquilibrium at heq
    rw [heq] at hCS
    have : e ≤ 0 := by exact_mod_cast hCS
    linarith
