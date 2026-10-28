-- Prove2me | solution 1 for FinancialDerivatives.FD03.finiteBinomial_pricing_and_optimal_exercise
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T08:13:18.828679+00:00
-- url     : https://prove2.me/submissions/de5c02a8-aed7-4bc3-8075-4b4b938e871b

import Mathlib.Tactic
import Definitions.Def_fd03_localHedge
import Definitions.Def_fd03_quotedClaimArbitrage
import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_SelfFinancing
import Definitions.Def_fd03_hedgeTerminalPays
import Definitions.Def_fd03_hedgeWealth
import Definitions.Def_fd03_europeanValue
import Definitions.Def_fd03_quotedClaimArbitrage
import Definitions.Def_fd03_admissible
import Definitions.Def_fd03_policyValue
import Definitions.Def_fd03_snellValue
import Definitions.Def_fd03_hedgeCoversExercise
import Definitions.Def_fd03_rowToRoot
import Definitions.Def_fd03_terminalRow
import Definitions.Def_fd03_payoffTreeMap
import Definitions.Def_fd03_terminalStockTree

namespace S82FD

open FinancialDerivatives.FD03

theorem hud (m : BinomialMarket) : m.up - m.down ≠ 0 := by
  linarith [m.down_lt_growth, m.growth_lt_up]
theorem hgpos (m : BinomialMarket) : 0 < m.growth := by linarith [m.down_pos, m.down_lt_growth]
theorem hupos (m : BinomialMarket) : 0 < m.up := by
  linarith [m.down_pos, m.down_lt_growth, m.growth_lt_up]
theorem w0 (m : BinomialMarket) : 0 < upWeight m := by
  unfold upWeight
  exact div_pos (by linarith [m.down_lt_growth]) (by linarith [m.down_lt_growth, m.growth_lt_up])
theorem w1 (m : BinomialMarket) : upWeight m < 1 := by
  unfold upWeight
  rw [div_lt_one (by linarith [m.down_lt_growth, m.growth_lt_up])]
  linarith [m.growth_lt_up]

theorem sf_wealth (m : BinomialMarket) (spot sh b wu wd : ℝ)
    (h1 : sh * (spot * m.up) + b * m.growth = wu) (h2 : sh * (spot * m.down) + b * m.growth = wd) :
    sh * spot + b = oneStepValue m wu wd := by
  have := hud m
  have := (hgpos m).ne'
  rw [← h1, ← h2]
  unfold oneStepValue upWeight
  field_simp
  ring

theorem lh_up (m : BinomialMarket) (spot vu vd : ℝ) (hspot : 0 < spot) :
    (localHedge m spot vu vd).1 * (spot * m.up) + (localHedge m spot vu vd).2 * m.growth = vu := by
  have := hud m
  have := (hgpos m).ne'
  have := hspot.ne'
  unfold localHedge; dsimp only; field_simp; ring

theorem lh_dn (m : BinomialMarket) (spot vu vd : ℝ) (hspot : 0 < spot) :
    (localHedge m spot vu vd).1 * (spot * m.down) + (localHedge m spot vu vd).2 * m.growth = vd := by
  have := hud m
  have := (hgpos m).ne'
  have := hspot.ne'
  unfold localHedge; dsimp only; field_simp; ring

theorem lh_cost (m : BinomialMarket) (spot vu vd : ℝ) (hspot : 0 < spot) :
    (localHedge m spot vu vd).1 * spot + (localHedge m spot vu vd).2 = oneStepValue m vu vd := by
  have := hud m
  have := (hgpos m).ne'
  have := hspot.ne'
  unfold localHedge oneStepValue upWeight; dsimp only; field_simp; ring

theorem osv_lin (m : BinomialMarket) (a b c d u : ℝ) :
    oneStepValue m a b + u * oneStepValue m c d = oneStepValue m (a + u * c) (b + u * d) := by
  unfold oneStepValue; ring

theorem osv_nonneg (m : BinomialMarket) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ oneStepValue m x y := by
  unfold oneStepValue
  have := w0 m; have := w1 m; have := hgpos m
  apply div_nonneg _ this.le
  nlinarith

theorem osv_pos (m : BinomialMarket) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : 0 < x ∨ 0 < y) :
    0 < oneStepValue m x y := by
  unfold oneStepValue
  have := w0 m; have := w1 m; have := hgpos m
  apply div_pos _ this
  rcases h with h | h <;> nlinarith

/-- arbitrage construction: shifted replicator of `a • claim` with extra capital `k`. -/
theorem shifted (m : BinomialMarket) (n : ℕ) (claim : PayoffTree n) :
    ∀ (spot a k : ℝ), 0 < spot → 0 < k → ∃ hedge : HedgeTree n,
      SelfFinancing m n spot hedge ∧ hedgeWealth m n spot hedge = a * europeanValue m n claim + k ∧
      terminalCombinedNonnegative n hedge claim (-a) ∧
      terminalCombinedPositiveSomewhere n hedge claim (-a) := by
  induction claim with
  | leaf c =>
    intro spot a k _ hk
    refine ⟨.terminal (a * c + k), trivial, rfl, ?_, ?_⟩
    · show 0 ≤ a * c + k + -a * c; linarith
    · show 0 < a * c + k + -a * c; linarith
  | branch cu cd ihu ihd =>
    intro spot a k hspot hk
    have hkg : 0 < k * m.growth := mul_pos hk (hgpos m)
    obtain ⟨hu, hu1, hu2, hu3, hu4⟩ := ihu (spot * m.up) a (k * m.growth) (mul_pos hspot (hupos m)) hkg
    obtain ⟨hd, hd1, hd2, hd3, hd4⟩ := ihd (spot * m.down) a (k * m.growth) (mul_pos hspot m.down_pos) hkg
    set Wu := a * europeanValue m _ cu + k * m.growth
    set Wd := a * europeanValue m _ cd + k * m.growth
    refine ⟨.node (localHedge m spot Wu Wd).1 (localHedge m spot Wu Wd).2 hu hd,
      ⟨?_, ?_, hu1, hd1⟩, ?_, ⟨hu3, hd3⟩, Or.inl hu4⟩
    · rw [hu2]; exact lh_up m spot Wu Wd hspot
    · rw [hd2]; exact lh_dn m spot Wu Wd hspot
    · show _ * spot + _ = a * oneStepValue m _ _ + k
      rw [lh_cost m spot Wu Wd hspot]
      have := (hgpos m).ne'
      simp only [Wu, Wd]
      unfold oneStepValue
      field_simp
      ring

/-- valuation of a self-financing combined position is nonneg / positive. -/
theorem value_bound (m : BinomialMarket) (n : ℕ) (hedge : HedgeTree n) :
    ∀ (spot : ℝ) (claim : PayoffTree n) (units : ℝ), SelfFinancing m n spot hedge →
      terminalCombinedNonnegative n hedge claim units →
      0 ≤ hedgeWealth m n spot hedge + units * europeanValue m n claim ∧
      (terminalCombinedPositiveSomewhere n hedge claim units →
        0 < hedgeWealth m n spot hedge + units * europeanValue m n claim) := by
  induction hedge with
  | terminal cash =>
    intro spot claim units _ hn
    cases claim with
    | leaf p => exact ⟨hn, fun h => h⟩
  | node sh b hu hd ihu ihd =>
    intro spot claim units hsf hn
    cases claim with
    | branch cu cd =>
      obtain ⟨h1, h2, h3, h4⟩ := hsf
      obtain ⟨n1, n2⟩ := hn
      obtain ⟨a1, a2⟩ := ihu _ cu units h3 n1
      obtain ⟨b1, b2⟩ := ihd _ cd units h4 n2
      have e : hedgeWealth m _ spot (.node sh b hu hd) + units * europeanValue m _ (.branch cu cd) =
          oneStepValue m (hedgeWealth m _ (spot * m.up) hu + units * europeanValue m _ cu)
            (hedgeWealth m _ (spot * m.down) hd + units * europeanValue m _ cd) := by
        show sh * spot + b + units * oneStepValue m _ _ = _
        rw [sf_wealth m spot sh b _ _ h1 h2, osv_lin]
      rw [e]
      refine ⟨osv_nonneg m _ _ a1 b1, fun hp => osv_pos m _ _ a1 b1 ?_⟩
      rcases hp with hp | hp
      · exact Or.inl (a2 hp)
      · exact Or.inr (b2 hp)

theorem noarb (m : BinomialMarket) (n : ℕ) (spot : ℝ) (hspot : 0 < spot)
    (claim : PayoffTree n) (quote : ℝ) :
    ¬ quotedClaimArbitrage m n spot claim quote ↔ quote = europeanValue m n claim := by
  constructor
  · intro h
    by_contra hne
    apply h
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · obtain ⟨hedge, h1, h2, h3, h4⟩ := shifted m n claim spot (-1) (europeanValue m n claim - quote)
        hspot (by linarith)
      refine ⟨hedge, 1, h1, ?_, by simpa using h3, by simpa using h4⟩
      rw [h2]; ring
    · obtain ⟨hedge, h1, h2, h3, h4⟩ := shifted m n claim spot 1 (quote - europeanValue m n claim)
        hspot (by linarith)
      refine ⟨hedge, -1, h1, ?_, h3, h4⟩
      rw [h2]; ring
  · rintro rfl ⟨hedge, units, h1, h2, h3, h4⟩
    have := (value_bound m n hedge spot claim units h1 h3).2 h4
    linarith

end S82FD

namespace S82FD2
open FinancialDerivatives.FD03

theorem recH (m : BinomialMarket) (n : ℕ)
    (spot : ℝ) (hspot : 0 < spot) (claim : PayoffTree n) :
    ∃ hedge : HedgeTree n,
      SelfFinancing m n spot hedge ∧
      hedgeTerminalPays n hedge claim ∧
      hedgeWealth m n spot hedge = europeanValue m n claim := by
  have hud : m.up - m.down ≠ 0 := by linarith [m.down_lt_growth, m.growth_lt_up]
  have hg : m.growth ≠ 0 := by linarith [m.down_pos, m.down_lt_growth]
  have hupos : 0 < m.up := by linarith [m.down_pos, m.down_lt_growth, m.growth_lt_up]
  induction claim generalizing spot with
  | leaf c => exact ⟨.terminal c, trivial, rfl, rfl⟩
  | branch cu cd ihu ihd =>
    obtain ⟨hu, hu1, hu2, hu3⟩ := ihu (spot * m.up) (mul_pos hspot hupos)
    obtain ⟨hd, hd1, hd2, hd3⟩ := ihd (spot * m.down) (mul_pos hspot m.down_pos)
    have hs : spot ≠ 0 := hspot.ne'
    refine ⟨.node (localHedge m spot (europeanValue m _ cu) (europeanValue m _ cd)).1
      (localHedge m spot (europeanValue m _ cu) (europeanValue m _ cd)).2 hu hd, ⟨?_, ?_, hu1, hd1⟩, ⟨hu2, hd2⟩, ?_⟩
    · rw [hu3]; unfold localHedge; dsimp only; field_simp; ring
    · rw [hd3]; unfold localHedge; dsimp only; field_simp; ring
    · show _ * spot + _ = oneStepValue m _ _
      unfold localHedge oneStepValue upWeight; dsimp only; field_simp; ring



theorem sfUniq (m : BinomialMarket)
    (n : ℕ) (spot : ℝ) (hspot : 0 < spot)
    (claim : PayoffTree n) (hedge : HedgeTree n)
    (hsf : SelfFinancing m n spot hedge)
    (hrep : hedgeTerminalPays n hedge claim) :
    hedgeWealth m n spot hedge = europeanValue m n claim := by
  have hud : m.up - m.down ≠ 0 := by linarith [m.down_lt_growth, m.growth_lt_up]
  have hg : m.growth ≠ 0 := by linarith [m.down_pos, m.down_lt_growth]
  have hupos : 0 < m.up := by linarith [m.down_pos, m.down_lt_growth, m.growth_lt_up]
  induction hedge generalizing spot with
  | terminal cash => cases claim; exact hrep
  | node sh b up dn ihu ihd =>
    cases claim with
    | branch cu cd =>
      obtain ⟨h1, h2, h3, h4⟩ := hsf
      obtain ⟨r1, r2⟩ := hrep
      show sh * spot + b = oneStepValue m _ _
      rw [← ihu _ (mul_pos hspot hupos) cu h3 r1, ← ihd _ (mul_pos hspot m.down_pos) cd h4 r2, ← h1, ← h2]
      unfold oneStepValue upWeight
      field_simp
      ring



theorem snMax (m : BinomialMarket) (n : ℕ)
    (exercise : ExerciseTree n) :
    ∃ p : StoppingPolicy n,
      admissible exercise p ∧
      policyValue m n exercise p = snellValue m n exercise ∧
      ∀ other : StoppingPolicy n,
        admissible exercise other →
          policyValue m n exercise other ≤ policyValue m n exercise p := by
  have mono : ∀ u₁ u₂ d₁ d₂ : ℝ, u₁ ≤ u₂ → d₁ ≤ d₂ → oneStepValue m u₁ d₁ ≤ oneStepValue m u₂ d₂ := by
    intro u₁ u₂ d₁ d₂ hu hd
    unfold oneStepValue
    have h0 : 0 < upWeight m := by
      unfold upWeight
      exact div_pos (by linarith [m.down_lt_growth]) (by linarith [m.down_lt_growth, m.growth_lt_up])
    have h1 : upWeight m < 1 := by
      unfold upWeight
      rw [div_lt_one (by linarith [m.down_lt_growth, m.growth_lt_up])]
      linarith [m.growth_lt_up]
    have hg : 0 < m.growth := by linarith [m.down_pos, m.down_lt_growth]
    apply div_le_div_of_nonneg_right _ hg.le
    nlinarith
  have le : ∀ (n : ℕ) (tree : ExerciseTree n) (p : StoppingPolicy n), admissible tree p →
      policyValue m n tree p ≤ snellValue m n tree := by
    intro n tree p hp
    induction tree with
    | maturity r => cases p; rfl
    | node a r u d ihu ihd =>
      cases p with
      | stop =>
        simp only [admissible] at hp
        subst hp
        exact le_max_left _ _
      | «continue» pu pd =>
        obtain ⟨h1, h2⟩ := hp
        have hc : policyValue m _ (.node a r u d) (.continue pu pd) ≤
            oneStepValue m (snellValue m _ u) (snellValue m _ d) := mono _ _ _ _ (ihu pu h1) (ihd pd h2)
        cases a
        · exact hc
        · exact hc.trans (le_max_right _ _)
  have ex : ∀ (n : ℕ) (tree : ExerciseTree n), ∃ p : StoppingPolicy n,
      admissible tree p ∧ policyValue m n tree p = snellValue m n tree := by
    intro n tree
    induction tree with
    | maturity r => exact ⟨.maturity, trivial, rfl⟩
    | node a r u d ihu ihd =>
      obtain ⟨pu, hu1, hu2⟩ := ihu
      obtain ⟨pd, hd1, hd2⟩ := ihd
      cases a
      · refine ⟨.continue pu pd, ⟨hu1, hd1⟩, ?_⟩
        show oneStepValue m _ _ = oneStepValue m _ _
        rw [hu2, hd2]
      · by_cases h : oneStepValue m (snellValue m _ u) (snellValue m _ d) ≤ r
        · refine ⟨.stop, rfl, ?_⟩
          show r = max r _
          exact (max_eq_left h).symm
        · refine ⟨.continue pu pd, ⟨hu1, hd1⟩, ?_⟩
          show oneStepValue m _ _ = max r (oneStepValue m _ _)
          rw [hu2, hd2, max_eq_right (le_of_lt (not_le.mp h))]
  obtain ⟨p, hp1, hp2⟩ := ex n exercise
  exact ⟨p, hp1, hp2, fun o ho => hp2 ▸ le n exercise o ho⟩



theorem wEx (m : BinomialMarket)
    (n : ℕ) (spot : ℝ) (hspot : 0 < spot)
    (exercise : ExerciseTree n) :
    ∃ hedge : HedgeTree n,
      SelfFinancing m n spot hedge ∧
      hedgeCoversExercise m n spot hedge exercise ∧
      hedgeWealth m n spot hedge = snellValue m n exercise := by
  have hud : m.up - m.down ≠ 0 := by linarith [m.down_lt_growth, m.growth_lt_up]
  have hg : m.growth ≠ 0 := by linarith [m.down_pos, m.down_lt_growth]
  have hupos : 0 < m.up := by linarith [m.down_pos, m.down_lt_growth, m.growth_lt_up]
  have gen : ∀ (n : ℕ) (spot capital : ℝ), 0 < spot → ∀ (exercise : ExerciseTree n),
      snellValue m n exercise ≤ capital → ∃ hedge : HedgeTree n,
      SelfFinancing m n spot hedge ∧ hedgeCoversExercise m n spot hedge exercise ∧
      hedgeWealth m n spot hedge = capital := by
    intro n spot capital hspot exercise hcapital
    induction exercise generalizing spot capital with
    | maturity r => exact ⟨.terminal capital, trivial, hcapital, rfl⟩
    | node a r uE dE ihu ihd =>
      have hs : spot ≠ 0 := hspot.ne'
      have hgp : 0 < m.growth := by linarith [m.down_pos, m.down_lt_growth]
      set Vu := snellValue m _ uE
      set Vd := snellValue m _ dE
      have hC : oneStepValue m Vu Vd ≤ capital := by
        refine le_trans ?_ hcapital
        cases a
        · exact le_rfl
        · exact le_max_right _ _
      have hR : a = true → r ≤ capital := by
        rintro rfl
        exact le_trans (le_max_left _ _) hcapital
      set e := capital - oneStepValue m Vu Vd with he
      have he0 : 0 ≤ e := by linarith
      obtain ⟨hu, hu1, hu2, hu3⟩ := ihu (spot * m.up) (Vu + e * m.growth) (mul_pos hspot hupos)
        (by nlinarith)
      obtain ⟨hd, hd1, hd2, hd3⟩ := ihd (spot * m.down) (Vd + e * m.growth) (mul_pos hspot m.down_pos)
        (by nlinarith)
      have hcost : (localHedge m spot Vu Vd).1 * spot + ((localHedge m spot Vu Vd).2 + e) = capital := by
        rw [he]
        unfold localHedge oneStepValue upWeight; dsimp only; field_simp; ring
      refine ⟨.node (localHedge m spot Vu Vd).1 ((localHedge m spot Vu Vd).2 + e) hu hd,
        ⟨?_, ?_, hu1, hd1⟩, ⟨fun ha => (hR ha).trans hcost.ge, hu2, hd2⟩, hcost⟩
      · rw [hu3]; unfold localHedge; dsimp only; field_simp; ring
      · rw [hd3]; unfold localHedge; dsimp only; field_simp; ring
  exact gen n spot _ hspot exercise le_rfl



theorem wLow (m : BinomialMarket)
    (n : ℕ) (spot : ℝ) (hspot : 0 < spot)
    (exercise : ExerciseTree n) (hedge : HedgeTree n)
    (hsf : SelfFinancing m n spot hedge)
    (hcover : hedgeCoversExercise m n spot hedge exercise) :
    snellValue m n exercise ≤ hedgeWealth m n spot hedge := by
  have hud : m.up - m.down ≠ 0 := by linarith [m.down_lt_growth, m.growth_lt_up]
  have hg : m.growth ≠ 0 := by linarith [m.down_pos, m.down_lt_growth]
  have hupos : 0 < m.up := by linarith [m.down_pos, m.down_lt_growth, m.growth_lt_up]
  have mono : ∀ u₁ u₂ d₁ d₂ : ℝ, u₁ ≤ u₂ → d₁ ≤ d₂ → oneStepValue m u₁ d₁ ≤ oneStepValue m u₂ d₂ := by
    intro u₁ u₂ d₁ d₂ hu hd
    unfold oneStepValue
    have h0 : 0 < upWeight m := by
      unfold upWeight
      exact div_pos (by linarith [m.down_lt_growth]) (by linarith [m.down_lt_growth, m.growth_lt_up])
    have h1 : upWeight m < 1 := by
      unfold upWeight
      rw [div_lt_one (by linarith [m.down_lt_growth, m.growth_lt_up])]
      linarith [m.growth_lt_up]
    have hg : 0 < m.growth := by linarith [m.down_pos, m.down_lt_growth]
    apply div_le_div_of_nonneg_right _ hg.le
    nlinarith
  induction hedge generalizing spot with
  | terminal cash => cases exercise; exact hcover
  | node sh b uH dH ihu ihd =>
    cases exercise with
    | node a r uE dE =>
      obtain ⟨h1, h2, h3, h4⟩ := hsf
      obtain ⟨c0, c1, c2⟩ := hcover
      have key : oneStepValue m (snellValue m _ uE) (snellValue m _ dE) ≤ sh * spot + b := by
        have e : sh * spot + b = oneStepValue m (hedgeWealth m _ (spot * m.up) uH)
            (hedgeWealth m _ (spot * m.down) dH) := by
          rw [← h1, ← h2]
          unfold oneStepValue upWeight
          field_simp
          ring
        rw [e]
        exact mono _ _ _ _ (ihu _ (mul_pos hspot hupos) _ h3 c1) (ihd _ (mul_pos hspot m.down_pos) _ h4 c2)
      show _ ≤ sh * spot + b
      cases a
      · exact key
      · exact max_le (c0 rfl) key



theorem recomb (m : BinomialMarket)
    (n : ℕ) (reward : ℝ → ℝ) :
    rowToRoot m n (terminalRow m n reward) =
      europeanValue m n
        (payoffTreeMap reward n (terminalStockTree m n m.initialSpot)) := by
  have step : ∀ (n : ℕ) (row : Fin (n + 2) → ℝ), rowToRoot m (n + 1) row =
      oneStepValue m (rowToRoot m n (fun k => row k.succ)) (rowToRoot m n (fun k => row k.castSucc)) := by
    intro n
    induction n with
    | zero => intro row; rfl
    | succ n ih =>
      intro row
      show rowToRoot m (n + 1) (backwardRow m (n + 1) row) = _
      rw [ih]
      rfl
  have gen : ∀ (n : ℕ) (s : ℝ) (f : ℝ → ℝ),
      rowToRoot m n (fun k => f (s * m.up ^ k.val * m.down ^ (n - k.val))) =
        europeanValue m n (payoffTreeMap f n (terminalStockTree m n s)) := by
    intro n
    induction n with
    | zero => intro s f; show f _ = f s; simp
    | succ n ih =>
      intro s f
      rw [step]
      show _ = oneStepValue m _ _
      rw [← ih (s * m.up) f, ← ih (s * m.down) f]
      congr 2
      · funext k
        congr 1
        simp only [Fin.val_succ, Nat.add_sub_add_right, pow_succ]
        ring
      · funext k
        congr 1
        simp only [Fin.coe_castSucc]
        rw [show n + 1 - k.val = (n - k.val) + 1 by have := k.isLt; omega, pow_succ]
        ring
  exact gen n m.initialSpot reward



end S82FD2

open FinancialDerivatives.FD03
theorem solution
    (m : BinomialMarket) (n : ℕ) (claim : PayoffTree n)
    (exercise : ExerciseTree n) (reward : ℝ → ℝ) :
    (∃ hedge : HedgeTree n,
      SelfFinancing m n m.initialSpot hedge ∧
      hedgeTerminalPays n hedge claim ∧
      hedgeWealth m n m.initialSpot hedge = europeanValue m n claim) ∧
    (∀ hedge : HedgeTree n,
      SelfFinancing m n m.initialSpot hedge →
      hedgeTerminalPays n hedge claim →
      hedgeWealth m n m.initialSpot hedge = europeanValue m n claim) ∧
    (∀ quote : ℝ,
      ¬ quotedClaimArbitrage m n m.initialSpot claim quote ↔
        quote = europeanValue m n claim) ∧
    (∃ p : StoppingPolicy n,
      admissible exercise p ∧
      policyValue m n exercise p = snellValue m n exercise ∧
      ∀ other : StoppingPolicy n,
        admissible exercise other →
          policyValue m n exercise other ≤ policyValue m n exercise p) ∧
    (∃ writer : HedgeTree n,
      SelfFinancing m n m.initialSpot writer ∧
      hedgeCoversExercise m n m.initialSpot writer exercise ∧
      hedgeWealth m n m.initialSpot writer = snellValue m n exercise) ∧
    (∀ writer : HedgeTree n,
      SelfFinancing m n m.initialSpot writer →
      hedgeCoversExercise m n m.initialSpot writer exercise →
      snellValue m n exercise ≤ hedgeWealth m n m.initialSpot writer) ∧
    rowToRoot m n (terminalRow m n reward) =
      europeanValue m n
        (payoffTreeMap reward n
          (terminalStockTree m n m.initialSpot)) := by
  have hs := m.initialSpot_pos
  refine ⟨S82FD2.recH m n m.initialSpot hs claim, fun h h1 h2 => S82FD2.sfUniq m n m.initialSpot hs claim h h1 h2,
    fun q => S82FD.noarb m n m.initialSpot hs claim q, S82FD2.snMax m n exercise,
    S82FD2.wEx m n m.initialSpot hs exercise, fun w h1 h2 => S82FD2.wLow m n m.initialSpot hs exercise w h1 h2,
    S82FD2.recomb m n reward⟩


