-- Prove2me | solution 1 for DaiWeissFluid.LBFS.drift_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T02:29:24.95939+00:00
-- url     : https://prove2.me/submissions/5cd732c5-9fb4-4775-961b-97b6db9d89ce

import Mathlib
import Definitions.Def_DaiWeissFluid_LBFS_FluidModel
import Theorems.Thm_DaiWeissFluid_LBFS_prop4_2

namespace DaiWeissFluid.LBFS

open Set Filter Topology

/-- Telescoping of the inflow terms: `∑_k μ_{k-1} T_{k-1}(s) = s + ∑_{k < K} μ_k T_k(s)`. -/
lemma db_inflow_sum {I K' : ℕ} (L : ReentrantLine I (K' + 1)) (T : ℝ → Fin (K' + 1) → ℝ)
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

/-- Total content identity `|Q(s)| = |Q(0)| + s - μ_K T_K(s)`. -/
lemma db_total {I K' : ℕ} (L : ReentrantLine I (K' + 1)) (Q T : ℝ → Fin (K' + 1) → ℝ)
    (hfs : L.IsFluidSolution Q T) (s : ℝ) (hs : 0 ≤ s) :
    ∑ k, Q s k = ∑ k, Q 0 k + s - L.μ (Fin.last K') * T s (Fin.last K') := by
  rw [Finset.sum_congr rfl (fun k _ => hfs.flow s hs k), Finset.sum_sub_distrib,
    Finset.sum_add_distrib, db_inflow_sum,
    Fin.sum_univ_castSucc (f := fun x => L.μ x * T s x)]
  ring

end DaiWeissFluid.LBFS

open DaiWeissFluid.LBFS Set Filter Topology in
theorem solution {I K : ℕ} (L : DaiWeissFluid.LBFS.ReentrantLine I K)
    (hm : ∀ k, 0 < L.m k) (hρ : ∀ i, L.ρ i < 1) (hK : 0 < K)
    (Q T : ℝ → Fin K → ℝ) (hsol : L.IsPrioritySolution Fin.revPerm Q T)
    (t : ℝ) (ht : 0 < t) (dT : Fin K → ℝ)
    (hdT : ∀ k, HasDerivAt (fun s => T s k) (dT k) t)
    (hpos : 0 < ∑ k, Q t k) (g : ℝ)
    (hg : HasDerivAt (fun s => ∑ k, Q s k) g t) :
    g ≤ 1 - L.lamHat ∧ 1 < L.lamHat := by
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  have hfs := hsol.1
  have hP := prop4_2 L hm Fin.revPerm Q T hsol t ht dT hdT
  -- the derivative of the total content
  have hG : g = 1 - L.outRate dT (Fin.last K') := by
    have h1 : HasDerivAt
        (fun s => ∑ k, Q 0 k + s - L.μ (Fin.last K') * T s (Fin.last K'))
        (0 + 1 - L.μ (Fin.last K') * dT (Fin.last K')) t :=
      ((hasDerivAt_const t _).add (hasDerivAt_id' t)).sub ((hdT _).const_mul _)
    have h2 : (fun s => ∑ k, Q s k) =ᶠ[𝓝 t]
        (fun s => ∑ k, Q 0 k + s - L.μ (Fin.last K') * T s (Fin.last K')) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      exact db_total L Q T hfs s (le_of_lt hs)
    have := hg.unique (h1.congr_of_eventuallyEq h2)
    simp only [ReentrantLine.outRate]; linarith
  -- the last nonempty buffer
  set S := Finset.univ.filter (fun k => 0 < Q t k) with hSdef
  have hSne : S.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have : ∀ k, Q t k = 0 := by
      intro k
      have hk : k ∉ S := by rw [hne]; simp
      simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hk
      exact le_antisymm hk (hfs.nonneg t ht.le k)
    simp [this] at hpos
  set k₀ := S.max' hSne with hk₀def
  have hk₀pos : 0 < Q t k₀ := by
    have := S.max'_mem hSne
    simpa [hSdef] using this
  have hafter : ∀ l, k₀ < l → Q t l = 0 := by
    intro l hl
    by_contra hne
    have hlS : l ∈ S := by
      simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and]
      exact lt_of_le_of_ne (hfs.nonneg t ht.le l) (Ne.symm hne)
    exact absurd (S.le_max' l hlS) (not_le.mpr hl)
  -- out-flow rates are constant from k₀ to the end of the route
  have hchain : ∀ j : ℕ, ∀ h : (k₀ : ℕ) + j < K' + 1,
      L.outRate dT ⟨(k₀ : ℕ) + j, h⟩ = L.outRate dT k₀ := by
    intro j
    induction j with
    | zero => intro h; rfl
    | succ j ih =>
      intro h
      have hlt : k₀ < (⟨(k₀ : ℕ) + (j + 1), h⟩ : Fin (K' + 1)) := by
        rw [Fin.lt_def]; simp
      have hb := hP.1 _ (hafter _ hlt)
      have hne : ((⟨(k₀ : ℕ) + (j + 1), h⟩ : Fin (K' + 1)) : ℕ) ≠ 0 := by simp
      simp only [ReentrantLine.inRate, hne, dite_false] at hb
      rw [← hb, ← ih (by omega)]
      congr 1
  have hconst : ∀ l, k₀ ≤ l → L.outRate dT l = L.outRate dT k₀ := by
    intro l hl
    have hl' : (k₀ : ℕ) ≤ l := hl
    have := hchain ((l : ℕ) - k₀) (by omega)
    have heq : (⟨(k₀ : ℕ) + ((l : ℕ) - k₀), by omega⟩ : Fin (K' + 1)) = l := by
      ext; simp; omega
    rwa [heq] at this
  have hc := (hP.2 k₀ hk₀pos (by
    intro l _ hl
    apply hafter
    simpa [Fin.revPerm_apply, Fin.rev_lt_rev] using hl)).1
  set d := L.outRate dT k₀ with hd
  set SH := ∑ k ∈ L.H Fin.revPerm k₀, L.m k with hSH
  have hH : ∀ k ∈ L.H Fin.revPerm k₀, k₀ ≤ k := by
    intro k hk
    simp only [ReentrantLine.H, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.revPerm_apply, Fin.rev_le_rev] at hk
    exact hk.2
  have hdS : d * SH = 1 := by
    rw [← hc, hSH, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hconst k (hH k hk)]; ring
  have hk₀H : k₀ ∈ L.H Fin.revPerm k₀ := by simp [ReentrantLine.H]
  have hSHpos : 0 < SH :=
    lt_of_lt_of_le (hm k₀) (Finset.single_le_sum (f := L.m) (fun k _ => (hm k).le) hk₀H)
  have hSHρ : SH ≤ L.ρ (L.σ k₀) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx
      simp only [ReentrantLine.H, ReentrantLine.C, Finset.mem_filter, Finset.mem_univ,
        true_and] at hx ⊢
      exact hx.1
    · intro k _ _; exact (hm k).le
  have : Nonempty (Fin I) := ⟨L.σ k₀⟩
  set M := ⨆ i : Fin I, L.ρ i with hM
  have hρM : L.ρ (L.σ k₀) ≤ M := le_ciSup (Finite.bddAbove_range _) _
  obtain ⟨i₀, hi₀⟩ := exists_eq_ciSup_of_finite (f := L.ρ)
  have hM1 : M < 1 := by rw [hM, ← hi₀]; exact hρ i₀
  have hMpos : 0 < M := by linarith
  have hlam : L.lamHat = 1 / M := rfl
  have hdval : d = 1 / SH := by rw [eq_div_iff hSHpos.ne']; exact hdS
  have hlast : L.outRate dT (Fin.last K') = d := hconst _ (Fin.le_last _)
  refine ⟨?_, ?_⟩
  · rw [hG, hlast, hdval, hlam]
    have : 1 / M ≤ 1 / SH := one_div_le_one_div_of_le hSHpos (le_trans hSHρ hρM)
    linarith
  · rw [hlam, lt_div_iff₀ hMpos]; linarith
