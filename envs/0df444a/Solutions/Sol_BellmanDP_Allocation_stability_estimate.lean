-- Prove2me | solution 1 for BellmanDP.Allocation.stability_estimate
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T12:09:10.765175+00:00
-- url     : https://prove2.me/submissions/709c60aa-2259-4c45-9c00-40f08353b7df

import Mathlib
import Definitions.Def_BellmanDP_Allocation_GeneralEquation



namespace BellmanDP.Allocation

lemma tri_le_aux {w : ℝ → ℝ → ℝ}
    (hw : ContinuousOn (fun p : ℝ × ℝ => w p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)))
    {x y z : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) (hxz : x ≤ z) :
    w x y ≤ triangleMax w z := by
  unfold triangleMax
  set Tr : Set (ℝ × ℝ) := {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ z} with hTr
  have hsub : Tr ⊆ Set.Icc 0 z ×ˢ Set.Icc 0 z := by
    rintro ⟨p1, p2⟩ ⟨h1, h2, h3⟩
    exact ⟨⟨by linarith, h3⟩, ⟨h1, by linarith⟩⟩
  have hcl : IsClosed Tr := by
    simp only [hTr, Set.setOf_and]
    refine (isClosed_le continuous_const continuous_snd).inter
      ((isClosed_le continuous_snd continuous_fst).inter (isClosed_le continuous_fst continuous_const))
  have hK : IsCompact Tr := (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hcl hsub
  have hcont : ContinuousOn (fun p : ℝ × ℝ => w p.1 p.2) Tr :=
    hw.mono (fun p hp => ⟨Set.mem_Ici.2 (by linarith [hp.1, hp.2.1]), Set.mem_Ici.2 hp.1⟩)
  exact le_csSup (hK.image_of_continuousOn hcont).bddAbove ⟨(x, y), ⟨hy, hyx, hxz⟩, rfl⟩

theorem stab_core (u v : ℝ → ℝ → ℝ) (a b : ℝ)
    (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1)
    (hu : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)))
    (hv : ContinuousOn (fun p : ℝ × ℝ => v p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)))
    (hD : ∀ z : ℝ, 0 ≤ z → Summable (fun n : ℕ =>
      triangleMax (fun s t => |u s t - v s t|) (max a b ^ n * z)))
    (f F : ℝ → ℝ)
    (hfc : ContinuousOn f (Set.Ici 0)) (hf0 : f 0 = 0) (hf : IsGeneralSolution u a b f)
    (hFc : ContinuousOn F (Set.Ici 0)) (hF0 : F 0 = 0) (hF : IsGeneralSolution v a b F) :
    ∀ x : ℝ, 0 ≤ x →
      |f x - F x| ≤ ∑' n : ℕ, triangleMax (fun s t => |u s t - v s t|) (max a b ^ n * x) := by
  intro x hx
  set c := max a b with hc
  have hc0 : 0 ≤ c := le_max_of_le_left ha0.le
  have hc1 : c < 1 := max_lt ha1 hb1
  set D : ℝ → ℝ := triangleMax (fun s t => |u s t - v s t|) with hDdef
  have hw : ContinuousOn (fun p : ℝ × ℝ => |u p.1 p.2 - v p.1 p.2|) (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)) :=
    (hu.sub hv).abs
  have triD : ∀ x y z : ℝ, 0 ≤ y → y ≤ x → x ≤ z → |u x y - v x y| ≤ D z :=
    fun x y z h1 h2 h3 => tri_le_aux (w := fun s t => |u s t - v s t|) hw h1 h2 h3
  -- one step
  have step : ∀ x, 0 ≤ x → ∃ y ∈ Set.Icc 0 x, ∃ z ∈ Set.Icc 0 (c * x),
      |f x - F x| ≤ |u x y - v x y| + |f z - F z| := by
    intro x hx
    obtain ⟨y1, hy1, e1⟩ := (hf x hx).1
    obtain ⟨y2, hy2, e2⟩ := (hF x hx).1
    have q1 := (hF x hx).2 ⟨y1, hy1, rfl⟩
    have p2 := (hf x hx).2 ⟨y2, hy2, rfl⟩
    simp only at e1 e2 q1 p2
    have zmem : ∀ y ∈ Set.Icc 0 x, a * y + b * (x - y) ∈ Set.Icc 0 (c * x) := by
      intro y hy
      have h0 := hy.1; have h1 : 0 ≤ x - y := by linarith [hy.2]
      have := ha0.le; have := hb0.le
      constructor
      · positivity
      · have := mul_le_mul_of_nonneg_right (le_max_left a b) h0
        have := mul_le_mul_of_nonneg_right (le_max_right a b) h1
        nlinarith
    rcases le_total (F x) (f x) with hpq | hpq
    · refine ⟨y1, hy1, _, zmem y1 hy1, ?_⟩
      rw [abs_of_nonneg (by linarith)]
      have := le_abs_self (u x y1 - v x y1)
      have := le_abs_self (f (a * y1 + b * (x - y1)) - F (a * y1 + b * (x - y1)))
      linarith
    · refine ⟨y2, hy2, _, zmem y2 hy2, ?_⟩
      rw [abs_of_nonpos (by linarith)]
      have := neg_le_abs (u x y2 - v x y2)
      have := neg_le_abs (f (a * y2 + b * (x - y2)) - F (a * y2 + b * (x - y2)))
      linarith
  have chain : ∀ N : ℕ, ∃ z ∈ Set.Icc 0 (c ^ N * x),
      |f x - F x| ≤ (∑ n ∈ Finset.range N, D (c ^ n * x)) + |f z - F z| := by
    intro N
    induction N with
    | zero => exact ⟨x, ⟨hx, by simp⟩, by simp⟩
    | succ N ih =>
      obtain ⟨z, hz, hle⟩ := ih
      obtain ⟨y, hy, z', hz', hle'⟩ := step z hz.1
      refine ⟨z', ⟨hz'.1, hz'.2.trans ?_⟩, ?_⟩
      · calc c * z ≤ c * (c ^ N * x) := mul_le_mul_of_nonneg_left hz.2 hc0
          _ = c ^ (N + 1) * x := by ring
      · rw [Finset.sum_range_succ]
        have := triD z y (c ^ N * x) hy.1 hy.2 hz.2
        linarith
  have Dnn : ∀ n : ℕ, 0 ≤ D (c ^ n * x) := fun n =>
    (abs_nonneg _).trans (triD 0 0 _ le_rfl le_rfl (by positivity))
  have he : ContinuousWithinAt (fun z => |f z - F z|) (Set.Ici 0) 0 :=
    ((hfc 0 (Set.mem_Ici.2 le_rfl)).sub (hFc 0 (Set.mem_Ici.2 le_rfl))).abs
  refine le_of_forall_pos_lt_add (fun ε hε => ?_)
  rw [Metric.continuousWithinAt_iff] at he
  obtain ⟨δ, hδ, hδ'⟩ := he ε hε
  have ht : Filter.Tendsto (fun n : ℕ => c ^ n * x) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const x
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hδ)).exists
  obtain ⟨z, hz, hle⟩ := chain n
  have := hδ' (x := z) (Set.mem_Ici.2 hz.1) (by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hz.1]; linarith [hz.2])
  simp only [hF0, hf0, sub_zero, Real.dist_eq, abs_abs, abs_zero] at this
  have hs : (∑ k ∈ Finset.range n, D (c ^ k * x)) ≤ ∑' k, D (c ^ k * x) :=
    (hD x hx).sum_le_tsum _ (fun k _ => Dnn k)
  linarith

end BellmanDP.Allocation

open BellmanDP.Allocation


theorem solution (u v : ℝ → ℝ → ℝ) (a b : ℝ)
    (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1)
    (hu : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)))
    (hv : ContinuousOn (fun p : ℝ × ℝ => v p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)))
    (hm : ∀ z : ℝ, 0 ≤ z → Summable (fun n : ℕ =>
      triangleMax (fun s t => max |u s t| |v s t|) (max a b ^ n * z)))
    (hD : ∀ z : ℝ, 0 ≤ z → Summable (fun n : ℕ =>
      triangleMax (fun s t => |u s t - v s t|) (max a b ^ n * z)))
    (f F : ℝ → ℝ)
    (hfc : ContinuousOn f (Set.Ici 0)) (hf0 : f 0 = 0) (hf : IsGeneralSolution u a b f)
    (hFc : ContinuousOn F (Set.Ici 0)) (hF0 : F 0 = 0) (hF : IsGeneralSolution v a b F) :
    ∀ x : ℝ, 0 ≤ x →
      |f x - F x| ≤ ∑' n : ℕ, triangleMax (fun s t => |u s t - v s t|) (max a b ^ n * x) := by
  exact stab_core u v a b ha0 ha1 hb0 hb1 hu hv hD f F hfc hf0 hf hFc hF0 hF
