-- Prove2me | solution 1 for BondySimonovits.cycle_construct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:11:12.174512+00:00
-- url     : https://prove2.me/submissions/64bc0156-531e-4985-aced-ffea1072876c

module
public import Definitions.Def_BondySimonovitsLib_BSLayers
public import Definitions.Def_BondySimonovitsLib_BSCycle
public import Theorems.Thm_BondySimonovits_anc_adj
public import Theorems.Thm_BondySimonovits_anc_anc
public import Theorems.Thm_BondySimonovits_anc_self
public import Theorems.Thm_BondySimonovits_anc_spec
public import Theorems.Thm_BondySimonovits_exists_isCycle_of_fn


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*} (K : SimpleGraph V) [DecidableRel K.Adj]
omit [DecidableRel K.Adj]
namespace BondySimonovits
theorem _root_.solution {par : V → V} {x : V}
    (hpar : ∀ v, K.Reachable x v → 0 < K.dist x v →
      K.Adj v (par v) ∧ K.dist x (par v) + 1 = K.dist x v)
    (k i j : ℕ) (hk : 2 ≤ k) (hik : i + 1 ≤ k) (hji' : j < i)
    (e : V) (q : ℕ → V) (m : ℕ) (hmdef : m = 2 * k - 2 * (i - j) - 1)
    (her : K.Reachable x e) (hel : K.dist x e = i) (hzr : K.Reachable x (q m))
    (hzl : K.dist x (q m) = i) (hwe : K.Adj e (q 0))
    (hqadj : ∀ t < m, K.Adj (q t) (q (t + 1))) (hqlev : ∀ t ≤ m, i ≤ K.dist x (q t))
    (hqinj : ∀ s ≤ m, ∀ t ≤ m, q s = q t → s = t) (hqe : ∀ t ≤ m, q t ≠ e)
    (hyz : anc K par x j (q m) = anc K par x j e)
    (hdiff : anc K par x (j + 1) e ≠ anc K par x (j + 1) (q m)) :
    ∃ (v : V) (p : K.Walk v v), p.IsCycle ∧ p.length = 2 * k := by
  obtain ⟨hh, hhdef⟩ : ∃ hh, hh = i - j := ⟨_, rfl⟩
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ, ℓ = 2 * k - 2 * hh := ⟨_, rfl⟩
  rw [← hhdef] at hmdef
  replace hmdef : m = ℓ - 1 := by omega
  -- the cycle as a sequence
  obtain ⟨c, hcdef⟩ : ∃ c : ℕ → V, c = fun t => if t ≤ hh then anc K par x (j + t) e else
    if t < hh + ℓ then q (t - hh - 1) else anc K par x (i - (t - hh - ℓ)) (q m) := ⟨_, rfl⟩
  have c_low : ∀ t, t ≤ hh → c t = anc K par x (j + t) e := fun t ht => by
    simp only [hcdef, ht, ↓reduceIte]
  have c_mid : ∀ t, hh < t → t < hh + ℓ → c t = q (t - hh - 1) := fun t h1 h2 => by
    have h3 : ¬ t ≤ hh := by omega
    simp only [hcdef, h3, h2, ↓reduceIte]
  have c_high : ∀ t, hh + ℓ ≤ t → c t = anc K par x (i - (t - hh - ℓ)) (q m) := fun t h1 => by
    have h3 : ¬ t ≤ hh := by omega
    have h4 : ¬ t < hh + ℓ := by omega
    simp only [hcdef, h3, h4, ↓reduceIte]
  have lev_low : ∀ t, t ≤ hh → K.dist x (c t) = j + t := fun t ht => by
    rw [c_low t ht]; exact (anc_spec hpar her (by omega)).2
  have lev_high : ∀ t, hh + ℓ ≤ t → t ≤ 2 * k →
      K.dist x (c t) = i - (t - hh - ℓ) := fun t ht ht' => by
    rw [c_high t ht]; exact (anc_spec hpar hzr (by omega)).2
  have lev_mid : ∀ t, hh < t → t < hh + ℓ → i ≤ K.dist x (c t) := fun t h1 h2 => by
    rw [c_mid t h1 h2]
    exact hqlev _ (by omega)
  apply exists_isCycle_of_fn K c (2 * k) (by omega)
  · -- consecutive vertices are adjacent
    intro t ht
    by_cases h1 : t + 1 ≤ hh
    · rw [c_low t (by omega), c_low (t + 1) h1]
      have hlt : j + t < K.dist x e := by omega
      have := anc_adj hpar her hlt
      rw [show j + (t + 1) = j + t + 1 by omega]
      exact this.symm
    by_cases h2 : t = hh
    · subst h2
      rw [c_low t le_rfl, c_mid (t + 1) (by omega) (by omega),
        show j + t = K.dist x e by omega, anc_self, show t + 1 - t - 1 = 0 by omega]
      exact hwe
    by_cases h3 : t + 1 < hh + ℓ
    · rw [c_mid t (by omega) (by omega), c_mid (t + 1) (by omega) h3,
        show t + 1 - hh - 1 = t - hh - 1 + 1 by omega]
      exact hqadj _ (by omega)
    by_cases h4 : t + 1 = hh + ℓ
    · rw [c_mid t (by omega) (by omega), c_high (t + 1) (by omega),
        show i - (t + 1 - hh - ℓ) = K.dist x (q m) by omega, anc_self,
        show t - hh - 1 = m - 1 by omega]
      have := hqadj (m - 1) (by omega)
      rwa [show m - 1 + 1 = m by omega] at this
    · rw [c_high t (by omega), c_high (t + 1) (by omega)]
      have := anc_adj hpar hzr (t := i - (t + 1 - hh - ℓ)) (by omega)
      rwa [show i - (t + 1 - hh - ℓ) + 1 = i - (t - hh - ℓ) by omega] at this
  · -- the sequence closes up
    rw [c_high (2 * k) (by omega), c_low 0 (by omega), show i - (2 * k - hh - ℓ) = j by omega,
      hyz, Nat.add_zero]
  · -- injectivity
    have key : ∀ s t, s < t → t < 2 * k → c s ≠ c t := by
      intro s t hst ht heq
      have hlev := congrArg (K.dist x) heq
      by_cases hs1 : s ≤ hh
      · by_cases ht1 : t ≤ hh
        · rw [lev_low s hs1, lev_low t ht1] at hlev
          omega
        by_cases ht2 : t < hh + ℓ
        · have := lev_mid t (by omega) ht2
          rw [lev_low s hs1] at hlev
          have hs : s = hh := by omega
          rw [c_low s hs1, c_mid t (by omega) ht2, show j + s = K.dist x e by omega,
            anc_self] at heq
          exact hqe _ (by omega) heq.symm
        · rw [lev_low s hs1, lev_high t (by omega) (by omega)] at hlev
          have e1 : anc K par x (j + 1) (c s) = anc K par x (j + 1) e := by
            rw [c_low s hs1]; exact anc_anc hpar her (by omega) (by omega)
          have e2 : anc K par x (j + 1) (c t) = anc K par x (j + 1) (q m) := by
            rw [c_high t (by omega)]; exact anc_anc hpar hzr (by omega) (by omega)
          rw [heq, e2] at e1
          exact hdiff e1.symm
      by_cases hs2 : s < hh + ℓ
      · by_cases ht2 : t < hh + ℓ
        · rw [c_mid s (by omega) hs2, c_mid t (by omega) ht2] at heq
          have := hqinj _ (by omega) _ (by omega) heq
          omega
        · have h5 := lev_mid s (by omega) hs2
          rw [lev_high t (by omega) (by omega)] at hlev
          rw [c_mid s (by omega) hs2, c_high t (by omega),
            show i - (t - hh - ℓ) = K.dist x (q m) by omega, anc_self] at heq
          have := hqinj _ (by omega) _ le_rfl heq
          omega
      · rw [lev_high s (by omega) (by omega), lev_high t (by omega) (by omega)] at hlev
        omega
    intro s hs t ht hst
    by_contra hne'
    rcases Nat.lt_or_gt_of_ne hne' with h | h
    · exact key s t h ht hst
    · exact key t s h hs hst.symm
end BondySimonovits
