-- Prove2me | solution 1 for DaiWeissFluid.FBFS.emptying_time
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T02:50:29.094575+00:00
-- url     : https://prove2.me/submissions/38fdd1da-d3fd-4639-93cb-5384e5c6c7ae

import Mathlib
import Definitions.Def_DaiWeissFluid_FBFS_FluidModel
import Theorems.Thm_DaiWeissFluid_FBFS_inductive_step

namespace DaiWeissFluid.FBFS

open Set

lemma fbfs_et_inflow_sum {I K' : ℕ} (L : ReentrantLine I (K' + 1)) (T : ℝ → Fin (K' + 1) → ℝ)
    (s : ℝ) :
    ∑ k, L.inflow T k s = s + ∑ i : Fin K', L.μ i.castSucc * T s i.castSucc := by
  have h0 : L.inflow T 0 s = s := by simp [ReentrantLine.inflow]
  rw [Fin.sum_univ_succ, h0]
  refine congrArg (s + ·) (Finset.sum_congr rfl ?_)
  intro i _
  have h1 : ((i.succ : Fin (K' + 1)) : ℕ) ≠ 0 := by simp
  simp only [ReentrantLine.inflow, h1, dite_false]
  have h2 : (⟨((i.succ : Fin (K' + 1)) : ℕ) - 1, by omega⟩ : Fin (K' + 1)) = i.castSucc := by
    ext; simp
  rw [h2]

/-- Total fluid: `|Q(t)| = |Q(0)| + t - μ_K T_K(t)`. -/
lemma fbfs_et_total {I K' : ℕ} (L : ReentrantLine I (K' + 1)) (Q T : ℝ → Fin (K' + 1) → ℝ)
    (hfs : L.IsFluidSolution Q T) (s : ℝ) (hs : 0 ≤ s) :
    ∑ k, Q s k = ∑ k, Q 0 k + s - L.μ (Fin.last K') * T s (Fin.last K') := by
  rw [Finset.sum_congr rfl (fun k _ => hfs.flow s hs k), Finset.sum_sub_distrib,
    Finset.sum_add_distrib, fbfs_et_inflow_sum,
    Fin.sum_univ_castSucc (f := fun x => L.μ x * T s x)]
  ring

/-- Peeling off the top index from a `(· : ℕ) < n + 1` filter of `Fin K`. -/
lemma fbfs_et_filter_succ {K : ℕ} (n : ℕ) (hn : n < K) :
    Finset.univ.filter (fun l : Fin K => (l : ℕ) < n + 1) =
      insert ⟨n, hn⟩ (Finset.univ.filter (fun l : Fin K => (l : ℕ) < n)) := by
  ext l
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
  omega

lemma fbfs_et_not_mem {K : ℕ} (n : ℕ) (hn : n < K) :
    (⟨n, hn⟩ : Fin K) ∉ Finset.univ.filter (fun l : Fin K => (l : ℕ) < n) := by
  simp

end DaiWeissFluid.FBFS

open DaiWeissFluid.FBFS Set in
theorem solution {I K : ℕ} (L : ReentrantLine I K) (hm : ∀ k, 0 < L.m k)
    (hρ : ∀ i, L.ρ i < 1) (Q T : ℝ → Fin K → ℝ) (hsol : L.IsPrioritySolution (fbfs K) Q T)
    (hQ0 : ∑ k, Q 0 k = 1) :
    ∀ t, L.fbfsEmptyingTime ≤ t → ∀ k, Q t k = 0 := by
  have hfs := hsol.1
  -- numerators `a_l = 1 - ∑_{H_l \ {l}} m` and denominators `b_l = 1 - ∑_{H_l} m`
  set a : Fin K → ℝ := fun l => 1 - ∑ j ∈ (L.H (fbfs K) l).erase l, L.m j with ha
  set b : Fin K → ℝ := fun l => 1 - ∑ j ∈ L.H (fbfs K) l, L.m j with hb
  have hab : ∀ l, a l = b l + L.m l := by
    intro l
    have hlH : l ∈ L.H (fbfs K) l := by simp [ReentrantLine.H]
    simp only [ha, hb, ← Finset.add_sum_erase _ _ hlH]
    ring
  have hbpos : ∀ l, 0 < b l := by
    intro l
    have hsub : L.H (fbfs K) l ⊆ L.C (L.σ l) := by
      intro x hx
      simp only [ReentrantLine.H, ReentrantLine.C, Finset.mem_filter, Finset.mem_univ,
        true_and] at hx ⊢
      exact hx.1
    have : ∑ j ∈ L.H (fbfs K) l, L.m j ≤ L.ρ (L.σ l) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => (hm j).le)
    have := hρ (L.σ l)
    simp only [hb]; linarith
  have hapos : ∀ l, 0 < a l := fun l => by rw [hab]; linarith [hbpos l, hm l]
  set N : ℕ → ℝ := fun n => ∏ l ∈ Finset.univ.filter (fun l : Fin K => (l : ℕ) < n), a l with hN
  set D : ℕ → ℝ := fun n => ∏ l ∈ Finset.univ.filter (fun l : Fin K => (l : ℕ) < n), b l with hD
  have hNpos : ∀ n, 0 < N n := fun n => Finset.prod_pos (fun l _ => hapos l)
  have hDpos : ∀ n, 0 < D n := fun n => Finset.prod_pos (fun l _ => hbpos l)
  -- the increments `t_k - t_{k-1}`
  set inc : Fin K → ℝ := fun k => L.m k *
      ((∏ l ∈ Finset.univ.filter (fun l : Fin K => l < k), a l) /
        ∏ l ∈ Finset.univ.filter (fun l : Fin K => l ≤ k), b l) with hinc
  have hinc' : ∀ k : Fin K, inc k = L.m k * (N k / D (k + 1)) := by
    intro k
    simp only [hinc, hN, hD]
    congr 3
    all_goals (ext l; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def,
      Fin.le_def]; try omega)
  have hincnn : ∀ k, 0 ≤ inc k := fun k => by
    rw [hinc' k]; exact mul_nonneg (hm k).le (div_nonneg (hNpos _).le (hDpos _).le)
  set tt : ℕ → ℝ := fun n => ∑ k ∈ Finset.univ.filter (fun k : Fin K => (k : ℕ) < n), inc k
    with htt
  have htt_nn : ∀ n, 0 ≤ tt n := fun n => Finset.sum_nonneg (fun k _ => hincnn k)
  have htt_succ : ∀ n (hn : n < K), tt (n + 1) = tt n + inc ⟨n, hn⟩ := by
    intro n hn
    simp only [htt]
    rw [fbfs_et_filter_succ n hn, Finset.sum_insert (fbfs_et_not_mem n hn)]
    ring
  have hN_succ : ∀ n (hn : n < K), N (n + 1) = N n * a ⟨n, hn⟩ := by
    intro n hn
    simp only [hN]
    rw [fbfs_et_filter_succ n hn, Finset.prod_insert (fbfs_et_not_mem n hn)]
    ring
  have hD_succ : ∀ n (hn : n < K), D (n + 1) = D n * b ⟨n, hn⟩ := by
    intro n hn
    simp only [hD]
    rw [fbfs_et_filter_succ n hn, Finset.prod_insert (fbfs_et_not_mem n hn)]
    ring
  -- `1 + t_n = N n / D n`
  have hclosed : ∀ n, n ≤ K → 1 + tt n = N n / D n := by
    intro n
    induction n with
    | zero =>
      intro _
      simp [htt, hN, hD]
    | succ n ih =>
      intro hn
      have hn' : n < K := by omega
      rw [htt_succ n hn', hN_succ n hn', hD_succ n hn', ← add_assoc, ih (by omega),
        hinc' ⟨n, hn'⟩]
      simp only []
      rw [hD_succ n hn', hab]
      have h1 := hDpos n
      have h2 := hbpos ⟨n, hn'⟩
      field_simp
      try ring
  -- the total fluid at time `t` is at most `1 + t`
  have htot : ∀ s, 0 ≤ s → ∀ k, Q s k ≤ 1 + s := by
    intro s hs k
    rcases Nat.eq_zero_or_pos K with hK | hK
    · subst hK; exact k.elim0
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    have h1 : Q s k ≤ ∑ j, Q s j :=
      Finset.single_le_sum (f := fun j => Q s j) (fun j _ => hfs.nonneg s hs j)
        (Finset.mem_univ k)
    have h2 := fbfs_et_total L Q T hfs s hs
    have h3 : 0 ≤ L.μ (Fin.last K') * T s (Fin.last K') := by
      apply mul_nonneg (inv_nonneg.mpr (hm _).le)
      have := hfs.T_mono (Fin.last K') (show (0 : ℝ) ∈ Ici (0 : ℝ) from Set.mem_Ici.mpr le_rfl) hs hs
      simp only [hfs.T_zero] at this; exact this
    linarith
  -- the induction over classes
  have hmain : ∀ n, n ≤ K → ∀ s, tt n ≤ s → ∀ l : Fin K, (l : ℕ) < n → Q s l = 0 := by
    intro n
    induction n with
    | zero => intro _ s _ l hl; omega
    | succ n ih =>
      intro hn s hs l hl
      have hn' : n < K := by omega
      set k : Fin K := ⟨n, hn'⟩ with hk
      have hτ := htt_nn n
      have hs' : tt n ≤ s := by
        have := htt_succ n hn'; have := hincnn k; linarith
      rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl' | hl'
      · exact ih (by omega) s hs' l hl'
      · have hlk : l = k := Fin.ext hl'
        subst hlk
        have hprev : ∀ t, tt n ≤ t → ∀ l, l < k → Q t l = 0 :=
          fun t ht l hl => ih (by omega) t ht l hl
        apply inductive_step L hm hρ Q T hsol k (tt n) hτ hprev s
        -- `Q_k(t_{k-1}) m_k / b_k ≤ t_k - t_{k-1}`
        have hQle := htot (tt n) hτ k
        have hcl := hclosed n (by omega)
        have hstep := htt_succ n hn'
        have hik := hinc' k
        have hkn : ((k : Fin K) : ℕ) = n := rfl
        rw [hkn] at hik
        have hbk := hbpos k
        have hmk := hm k
        have : Q (tt n) k * L.m k / b k ≤ inc k := by
          rw [hik, mul_div_assoc', div_le_iff₀ hbk, hD_succ n hn']
          have e : L.m k * N n / (D n * b k) * b k = L.m k * (N n / D n) := by
            field_simp
          rw [e, ← hcl]
          nlinarith
        show tt n + Q (tt n) k * L.m k / b k ≤ s
        linarith
  -- `t_K` is the emptying time
  have hδ : L.fbfsEmptyingTime = tt K := by
    simp only [ReentrantLine.fbfsEmptyingTime, htt]
    rw [Finset.filter_true_of_mem (fun k _ => k.isLt)]
  intro t ht k
  exact hmain K le_rfl t (by rw [← hδ]; exact ht) k k.isLt
