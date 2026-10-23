-- Prove2me | solution 1 for Fundraising.PartialCollab.eq_S11
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T16:10:16.49436+00:00
-- url     : https://prove2.me/submissions/ee4d0019-6a0d-4573-91c8-48a8f946278d

import Mathlib
import Definitions.Def_Fundraising_PartialCollab_Setting

namespace FR3

open Set

/-- Abstract best-response characterization for the lexicographic problem (10). -/
theorem br_char (a b B X M : ℝ) (f C : ℝ → ℝ) (perfF gapF utilF : ℝ × ℝ → ℝ)
    (hB : 0 < B) (hX : 0 ≤ X)
    (hf : ∀ σ ∈ Icc a b, 0 < f σ)
    (hC : StrictMonoOn C (Icc 0 1))
    (σs : ℝ) (hσs : σs ∈ Icc a b) (hMdef : M = f σs) (hmax : ∀ σ ∈ Icc a b, f σ ≤ M)
    (hperf : ∀ p, perfF p = f p.1 * min (p.2 + X) 1)
    (hgap : ∀ p, gapF p = max (B - perfF p) 0)
    (hutil : ∀ p, utilF p = min (perfF p) B - C p.2)
    (p : ℝ × ℝ) (hp : p ∈ Icc a b ×ˢ Icc (0:ℝ) 1) :
    (p ∈ {p | p ∈ {p | p ∈ {p | p ∈ Icc a b ×ˢ Icc (0:ℝ) 1 ∧
          ∀ q ∈ Icc a b ×ˢ Icc (0:ℝ) 1, gapF p ≤ gapF q} ∧
        ∀ q ∈ {p | p ∈ Icc a b ×ˢ Icc (0:ℝ) 1 ∧
          ∀ q ∈ Icc a b ×ˢ Icc (0:ℝ) 1, gapF p ≤ gapF q}, utilF q ≤ utilF p} ∧
      ∀ q ∈ {p | p ∈ {p | p ∈ Icc a b ×ˢ Icc (0:ℝ) 1 ∧
          ∀ q ∈ Icc a b ×ˢ Icc (0:ℝ) 1, gapF p ≤ gapF q} ∧
        ∀ q ∈ {p | p ∈ Icc a b ×ˢ Icc (0:ℝ) 1 ∧
          ∀ q ∈ Icc a b ×ˢ Icc (0:ℝ) 1, gapF p ≤ gapF q}, utilF q ≤ utilF p},
        perfF q ≤ perfF p}) ↔
      f p.1 = M ∧ p.2 = max (min (B / M) 1 - X) 0 := by
  set K := Icc a b ×ˢ Icc (0:ℝ) 1 with hK
  set GM := {p | p ∈ K ∧ ∀ q ∈ K, gapF p ≤ gapF q} with hGM
  set UM := {p | p ∈ GM ∧ ∀ q ∈ GM, utilF q ≤ utilF p} with hUM
  have hMpos : 0 < M := hMdef ▸ hf σs hσs
  set m := min B M with hm
  set αs := min (B / M) 1 with hαs
  set ξ0 := max (αs - X) 0 with hξ0
  have hαs_pos : 0 < αs := lt_min (div_pos hB hMpos) one_pos
  have hαs_le : αs ≤ 1 := min_le_right _ _
  have hMα : M * αs = m := by
    rw [hαs, hm]
    rcases le_total B M with h | h
    · rw [min_eq_left ((div_le_one hMpos).2 h), min_eq_left h]; field_simp
    · rw [min_eq_right ((one_le_div hMpos).2 h), min_eq_right h, mul_one]
  have hξ0_nn : 0 ≤ ξ0 := le_max_right _ _
  have hξ0_le : ξ0 ≤ 1 := max_le (by linarith) zero_le_one
  have hξ0X : αs ≤ ξ0 + X := by have := le_max_left (αs - X) 0; linarith
  have hρ : min (ξ0 + X) 1 ≥ αs := le_min hξ0X hαs_le
  -- P ≤ M on K
  have hPle : ∀ q ∈ K, perfF q ≤ M := by
    intro q hq
    rw [hperf]
    have h1 := hf q.1 hq.1
    have h2 := hmax q.1 hq.1
    have h3 : min (q.2 + X) 1 ≤ 1 := min_le_right _ _
    nlinarith
  -- gap characterization
  have hgapGM : ∀ q ∈ K, q ∈ GM ↔ m ≤ perfF q := by
    intro q hq
    have hs1 : (σs, (1:ℝ)) ∈ K := ⟨hσs, ⟨zero_le_one, le_refl _⟩⟩
    have hPs1 : perfF (σs, 1) = M := by
      rw [hperf, hMdef]; simp [min_eq_right (by linarith : (1:ℝ) ≤ 1 + X)]
    constructor
    · rintro ⟨_, hq2⟩
      have := hq2 _ hs1
      rw [hgap, hgap, hPs1] at this
      have hPq := hPle q hq
      rw [hm]
      rcases le_total B M with h | h
      · rw [min_eq_left h]
        rw [max_eq_right (by linarith : B - M ≤ 0)] at this
        have := le_max_left (B - perfF q) 0; linarith
      · rw [min_eq_right h]
        rw [max_eq_left (by linarith : 0 ≤ B - M)] at this
        have := le_max_left (B - perfF q) 0; linarith
    · intro hmq
      refine ⟨hq, fun r hr => ?_⟩
      rw [hgap, hgap]
      have hPr := hPle r hr
      rw [hm] at hmq
      rcases le_total B M with h | h
      · rw [min_eq_left h] at hmq
        rw [max_eq_right (by linarith : B - perfF q ≤ 0)]; exact le_max_right _ _
      · rw [min_eq_right h] at hmq
        exact max_le_max (by linarith) (le_refl _)
  -- min(P, B) = m on GM
  have hminGM : ∀ q ∈ GM, min (perfF q) B = m := by
    intro q hq
    have h1 := (hgapGM q hq.1).1 hq
    have h2 := hPle q hq.1
    rw [hm] at h1 ⊢
    rcases le_total B M with h | h
    · rw [min_eq_left h] at h1 ⊢; exact min_eq_right h1
    · rw [min_eq_right h] at h1 ⊢; rw [min_eq_left (by linarith)]; linarith
  -- (σ, ξ0) ∈ GM whenever f σ = M
  have hmemGM : ∀ σ ∈ Icc a b, f σ = M → (σ, ξ0) ∈ GM := by
    intro σ hσ hfσ
    have hq : (σ, ξ0) ∈ K := ⟨hσ, ⟨hξ0_nn, hξ0_le⟩⟩
    refine (hgapGM _ hq).2 ?_
    rw [hperf]; simp only
    rw [hfσ, ← hMα]
    exact mul_le_mul_of_nonneg_left hρ hMpos.le
  -- lower bound on effort in GM
  have hξlow : ∀ q ∈ GM, ξ0 ≤ q.2 := by
    intro q hq
    have hqK := hq.1
    have h1 := (hgapGM q hqK).1 hq
    rw [hperf] at h1
    have hfq := hf q.1 hqK.1
    have hfM := hmax q.1 hqK.1
    have hmin_nn : 0 ≤ min (q.2 + X) 1 := le_min (by linarith [hqK.2.1]) zero_le_one
    have h2 : M * αs ≤ M * min (q.2 + X) 1 := by rw [hMα]; nlinarith
    have h3 : αs ≤ min (q.2 + X) 1 := le_of_mul_le_mul_left h2 hMpos
    have h4 : αs ≤ q.2 + X := h3.trans (min_le_left _ _)
    exact max_le (by linarith) hqK.2.1
  -- UM characterization
  have hUMiff : ∀ q, q ∈ UM ↔ q ∈ GM ∧ q.2 = ξ0 := by
    intro q
    constructor
    · rintro ⟨hqGM, hq2⟩
      refine ⟨hqGM, le_antisymm ?_ (hξlow q hqGM)⟩
      have hsGM := hmemGM σs hσs hMdef.symm
      have := hq2 _ hsGM
      rw [hutil, hutil, hminGM _ hsGM, hminGM _ hqGM] at this
      have hc : C q.2 ≤ C ξ0 := by simp only at this; linarith
      exact (hC.le_iff_le ⟨hqGM.1.2.1, hqGM.1.2.2⟩ ⟨hξ0_nn, hξ0_le⟩).1 hc
    · rintro ⟨hqGM, hq2⟩
      refine ⟨hqGM, fun r hr => ?_⟩
      rw [hutil, hutil, hminGM _ hr, hminGM _ hqGM, hq2]
      have := hξlow r hr
      have hc : C ξ0 ≤ C r.2 :=
        (hC.le_iff_le ⟨hξ0_nn, hξ0_le⟩ ⟨hr.1.2.1, hr.1.2.2⟩).2 this
      linarith
  have hρpos : 0 < min (ξ0 + X) 1 := lt_of_lt_of_le hαs_pos hρ
  change (p ∈ UM ∧ ∀ q ∈ UM, perfF q ≤ perfF p) ↔ _
  constructor
  · rintro ⟨hpUM, hp2⟩
    have ⟨hpGM, hpξ⟩ := (hUMiff p).1 hpUM
    refine ⟨?_, hpξ⟩
    have hsUM : (σs, ξ0) ∈ UM := (hUMiff _).2 ⟨hmemGM σs hσs hMdef.symm, rfl⟩
    have := hp2 _ hsUM
    rw [hperf, hperf, hpξ] at this
    simp only at this
    rw [← hMdef] at this
    have := le_of_mul_le_mul_right this hρpos
    exact le_antisymm (hmax p.1 hp.1) this
  · rintro ⟨hfp, hpξ⟩
    have hpGM : p ∈ GM := by
      have := hmemGM p.1 hp.1 hfp
      rw [← hpξ] at this; simpa using this
    refine ⟨(hUMiff p).2 ⟨hpGM, hpξ⟩, fun q hq => ?_⟩
    have ⟨hqGM, hqξ⟩ := (hUMiff q).1 hq
    rw [hperf, hperf, hpξ, hqξ, hfp]
    exact mul_le_mul_of_nonneg_right (hmax q.1 hqGM.1.1) hρpos.le

end FR3

namespace Fundraising.PartialCollab

open Finset

theorem sum_exp_update {n : ℕ} (s : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    ∑ j, Real.exp (Function.update s i t j) =
      Real.exp t + ∑ j ∈ univ.erase i, Real.exp (s j) := by
  rw [← Finset.add_sum_erase _ _ (mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

theorem sum_update' {n : ℕ} (x : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    ∑ j, Function.update x i t j = t + ∑ j ∈ univ.erase i, x j := by
  rw [← Finset.add_sum_erase _ _ (mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

theorem theta_update {n : ℕ} (s : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    theta (Function.update s i t) i =
      Real.exp t / (1 + Real.exp t + ∑ j ∈ univ.erase i, Real.exp (s j)) := by
  unfold theta
  rw [sum_exp_update, Function.update_self, add_assoc]

theorem theta_update_pos {n : ℕ} (s : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    0 < theta (Function.update s i t) i := by
  rw [theta_update]
  have : 0 ≤ ∑ j ∈ univ.erase i, Real.exp (s j) :=
    Finset.sum_nonneg (fun j _ => (Real.exp_pos _).le)
  positivity

theorem theta_update_continuous {n : ℕ} (s : Fin n → ℝ) (i : Fin n) :
    Continuous (fun t => theta (Function.update s i t) i) := by
  have hR : 0 ≤ ∑ j ∈ univ.erase i, Real.exp (s j) :=
    Finset.sum_nonneg (fun j _ => (Real.exp_pos _).le)
  simp_rw [theta_update]
  exact Real.continuous_exp.div (by fun_prop) (fun t => by positivity)

/-- Best-response characterization for one HO. -/
theorem br_iff {n : ℕ} (G : Setting n) (hG : G.Standing) (s x : Fin n → ℝ) (i : Fin n)
    (hsi : s i ∈ Set.Icc (G.a i) (G.b i)) (hxi : x i ∈ Set.Icc (0:ℝ) 1)
    (hX : 0 ≤ ∑ j ∈ univ.erase i, x j) :
    (s i, x i) ∈ G.bestResponses s x i ↔
      IsMaxOn (fun t => G.δ i t * theta (Function.update s i t) i)
        (Set.Icc (G.a i) (G.b i)) (s i) ∧
      x i = max (G.alpha s i - ∑ j ∈ univ.erase i, x j) 0 := by
  obtain ⟨l, r, hl, hr, hδpos, hδdiff, _⟩ := hG.δ_regular i
  have hsub : Set.Icc (G.a i) (G.b i) ⊆ Set.Ioo l r := fun t ht =>
    ⟨lt_of_lt_of_le hl ht.1, lt_of_le_of_lt ht.2 hr⟩
  set f := fun t => G.δ i t * theta (Function.update s i t) i with hfdef
  have hfpos : ∀ σ ∈ Set.Icc (G.a i) (G.b i), 0 < f σ := fun σ hσ =>
    mul_pos (hδpos σ (hsub hσ)) (theta_update_pos s i σ)
  have hfcont : ContinuousOn f (Set.Icc (G.a i) (G.b i)) :=
    (hδdiff.continuousOn.mono hsub).mul (theta_update_continuous s i).continuousOn
  obtain ⟨σs, hσs, hσmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.2 (hG.a_le_b i)) hfcont
  set X := ∑ j ∈ univ.erase i, x j with hXdef
  have key := FR3.br_char (G.a i) (G.b i) (G.B i) X (f σs) f (G.C i)
    (fun p => G.perf (Function.update s i p.1) (Function.update x i p.2) i)
    (fun p => G.gap (Function.update s i p.1) (Function.update x i p.2) i)
    (fun p => G.utility (Function.update s i p.1) (Function.update x i p.2) i)
    (hG.B_pos i) hX hfpos (hG.C_strictMonoOn i) σs hσs rfl
    (fun σ hσ => isMaxOn_iff.1 hσmax σ hσ)
    (by
      intro p
      simp only [Setting.perf, expDonation, reach, Function.update_self, sum_update', hfdef]
      ring)
    (fun p => rfl)
    (by intro p; simp only [Setting.utility, Function.update_self])
    (s i, x i) ⟨hsi, hxi⟩
  have hfsi : f (s i) = G.δ i (s i) * theta s i := by
    simp only [hfdef, Function.update_eq_self]
  refine key.trans ?_
  simp only
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨isMaxOn_iff.2 (fun σ hσ => ?_), ?_⟩
    · rw [h1]; exact isMaxOn_iff.1 hσmax σ hσ
    · rw [h2, Setting.alpha, ← hfsi, h1]
  · rintro ⟨h1, h2⟩
    have hle := isMaxOn_iff.1 h1 σs hσs
    have hge := isMaxOn_iff.1 hσmax (s i) hsi
    have heq : f (s i) = f σs := le_antisymm hge hle
    refine ⟨heq, ?_⟩
    rw [h2, Setting.alpha, ← hfsi, heq]

theorem eq_S11 {n : ℕ} (G : Setting n) (hG : G.Standing) (s x : Fin n → ℝ)
    (hbox : G.InBox s x) :
    G.IsNE s x ↔ ∀ i : Fin n,
      IsMaxOn (fun t => G.δ i t * theta (Function.update s i t) i)
        (Set.Icc (G.a i) (G.b i)) (s i) ∧
      x i = max (G.alpha s i - ∑ j ∈ univ.erase i, x j) 0 := by
  have hX : ∀ i, 0 ≤ ∑ j ∈ univ.erase i, x j :=
    fun i => Finset.sum_nonneg (fun j _ => (hbox j).2.1)
  unfold Setting.IsNE
  constructor
  · rintro ⟨_, h⟩ i
    exact (br_iff G hG s x i (hbox i).1 (hbox i).2 (hX i)).1 (h i)
  · intro h
    exact ⟨hbox, fun i => (br_iff G hG s x i (hbox i).1 (hbox i).2 (hX i)).2 (h i)⟩

end Fundraising.PartialCollab

open Fundraising.PartialCollab Finset in
theorem solution {n : ℕ} (G : Setting n) (hG : G.Standing) (s x : Fin n → ℝ)
    (hbox : G.InBox s x) :
    G.IsNE s x ↔ ∀ i : Fin n,
      IsMaxOn (fun t => G.δ i t * theta (Function.update s i t) i)
        (Set.Icc (G.a i) (G.b i)) (s i) ∧
      x i = max (G.alpha s i - ∑ j ∈ univ.erase i, x j) 0 :=
  eq_S11 G hG s x hbox
