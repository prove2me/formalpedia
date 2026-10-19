-- Prove2me | solution 1 for CrossLicensing.Innovation.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-18T09:27:08.260154+00:00
-- url     : https://prove2.me/submissions/b106c28d-9534-4e21-9296-e359e81f7652

-- Licensed under Apache 2.0. Complete cross-licensing innovation equilibrium.
import Mathlib
import Definitions.Def_CrossLicensing_Innovation_Model
import Definitions.Def_CrossLicensing_Innovation_ClosedForms


namespace CrossLicensingProof
open CrossLicensing.Innovation

noncomputable def slope (β k u v : ℝ) : ℝ :=
  (7 - 5 * β) * (2 - (5 - 7 * β) * v) - (144 * k - (7 - 5 * β) ^ 2) * u

structure CandidateCertificate (β k u v : ℝ) : Prop where
  own_nonneg : 0 ≤ u
  other_nonneg : 0 ≤ v
  lower : (Real.sqrt 3 - 1) * qual2 β u v ≤ qual1 β u v
  upper : (Real.sqrt 3 - 1) * qual1 β u v ≤ qual2 β u v
  optimal : slope β k u v = 0 ∨
    (β < Real.sqrt 3 - 1 ∧ u = That2 β v ∧ 0 ≤ slope β k u v)

end CrossLicensingProof


namespace CrossLicensingProof

noncomputable def revenue (l h p : ℝ) : ℝ :=
  if p ≤ 2 * l - h then p * (l + h - 2 * p) / 3
  else if p ≤ h then p * (h - p) / 2 else 0

lemma sqrt_three_bounds : (12 : ℝ) / 7 < Real.sqrt 3 ∧
    Real.sqrt 3 < 7 / 4 ∧ (Real.sqrt 3) ^ 2 = 3 := by
  have hp := Real.sqrt_nonneg (3 : ℝ)
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  constructor
  · nlinarith
  constructor
  · nlinarith
  · exact hs

lemma revenue_duo_bound (l h p : ℝ) :
    p * (l + h - 2 * p) / 3 ≤ (l + h) ^ 2 / 24 := by
  nlinarith [sq_nonneg (4 * p - l - h)]

lemma revenue_mono_bound (h p : ℝ) :
    p * (h - p) / 2 ≤ h ^ 2 / 8 := by
  nlinarith [sq_nonneg (2 * p - h)]

lemma supplier_value_compare {l h : ℝ} (hl : 0 < l) (hlh : l ≤ h) :
    (Real.sqrt 3 - 1) * h ≤ l ↔ h ^ 2 / 8 ≤ (l + h) ^ 2 / 24 := by
  have hh : 0 < h := lt_of_lt_of_le hl hlh
  obtain ⟨hslo, hshi, hs⟩ := sqrt_three_bounds
  have hmul : (Real.sqrt 3 * h) ^ 2 = 3 * h ^ 2 := by rw [mul_pow, hs]
  constructor
  · intro he
    have : Real.sqrt 3 * h ≤ l + h := by nlinarith
    have hx := (sq_le_sq₀ (by positivity : 0 ≤ Real.sqrt 3 * h) (by positivity : 0 ≤ l + h)).mpr this
    nlinarith
  · intro he
    by_contra hn
    have hx : l + h < Real.sqrt 3 * h := by nlinarith
    have hy := mul_pos (sub_pos.mpr hx) (show 0 < Real.sqrt 3 * h + (l + h) by positivity)
    nlinarith

lemma supplier_duo_attains {l h : ℝ} (hl : 0 < l) (hlh : l ≤ h)
    (hd : (Real.sqrt 3 - 1) * h ≤ l) :
    revenue l h ((l + h) / 4) = (l + h) ^ 2 / 24 := by
  have hh : 0 < h := lt_of_lt_of_le hl hlh
  obtain ⟨hslo, hshi, hs⟩ := sqrt_three_bounds
  have hx := mul_pos (show 0 < Real.sqrt 3 - 12 / 7 by linarith) hh
  have hp : (l + h) / 4 ≤ 2 * l - h := by nlinarith
  simp only [revenue, if_pos hp]
  ring

lemma supplier_mono_attains {l h : ℝ} (hl : 0 < l) (hlh : l ≤ h)
    (hd : ¬ (Real.sqrt 3 - 1) * h ≤ l) :
    revenue l h (h / 2) = h ^ 2 / 8 := by
  have hh : 0 < h := lt_of_lt_of_le hl hlh
  obtain ⟨hslo, hshi, hs⟩ := sqrt_three_bounds
  have hx := mul_pos (show 0 < 7 / 4 - Real.sqrt 3 by linarith) hh
  have hp : ¬ h / 2 ≤ 2 * l - h := by nlinarith
  simp only [revenue, if_neg hp, if_pos (show h / 2 ≤ h by linarith)]
  ring

lemma supplier_duo_least {l h : ℝ} (hl : 0 < l) (hlh : l ≤ h)
    (hd : (Real.sqrt 3 - 1) * h ≤ l) :
    IsLeast {p : ℝ | 0 ≤ p ∧ ∀ q, 0 ≤ q → revenue l h q ≤ revenue l h p}
      ((l + h) / 4) := by
  have hh : 0 < h := lt_of_lt_of_le hl hlh
  have he := supplier_duo_attains hl hlh hd
  have hv := (supplier_value_compare hl hlh).mp hd
  constructor
  · refine ⟨by positivity, ?_⟩
    intro q _
    rw [he]
    unfold revenue
    split_ifs
    · exact revenue_duo_bound l h q
    · exact (revenue_mono_bound h q).trans hv
    · positivity
  · intro p hp
    have hb := hp.2 ((l + h) / 4) (by positivity)
    rw [he] at hb
    unfold revenue at hb
    split_ifs at hb
    · nlinarith [sq_nonneg (4 * p - l - h)]
    · nlinarith [sq_nonneg (2 * p - h)]
    · nlinarith [sq_pos_of_pos (show 0 < l + h by positivity)]

lemma supplier_mono_least {l h : ℝ} (hl : 0 < l) (hlh : l ≤ h)
    (hd : ¬ (Real.sqrt 3 - 1) * h ≤ l) :
    IsLeast {p : ℝ | 0 ≤ p ∧ ∀ q, 0 ≤ q → revenue l h q ≤ revenue l h p}
      (h / 2) := by
  have hh : 0 < h := lt_of_lt_of_le hl hlh
  have he := supplier_mono_attains hl hlh hd
  have hv : (l + h) ^ 2 / 24 < h ^ 2 / 8 := lt_of_not_ge (by
    intro hn
    exact hd ((supplier_value_compare hl hlh).mpr hn))
  constructor
  · refine ⟨by positivity, ?_⟩
    intro q _
    rw [he]
    unfold revenue
    split_ifs
    · exact (revenue_duo_bound l h q).trans hv.le
    · exact revenue_mono_bound h q
    · positivity
  · intro p hp
    have hb := hp.2 (h / 2) (by positivity)
    rw [he] at hb
    unfold revenue at hb
    split_ifs at hb
    · have := revenue_duo_bound l h p
      linarith
    · nlinarith [sq_nonneg (2 * p - h)]
    · nlinarith [sq_pos_of_pos hh]

end CrossLicensingProof


namespace CrossLicensingProof
open CrossLicensing.Innovation

lemma supplierProfit_revenue (β u v p : ℝ) :
    supplierProfit β u v p = revenue (min (qual1 β u v) (qual2 β u v))
      (max (qual1 β u v) (qual2 β u v)) p := by
  by_cases hd : p ≤ 2 * min (qual1 β u v) (qual2 β u v) - max (qual1 β u v) (qual2 β u v)
  · simp only [supplierProfit, quantities, revenue, if_pos hd]
    rw [min_add_max]
    ring
  · by_cases hm : p ≤ max (qual1 β u v) (qual2 β u v)
    · by_cases hab : qual1 β u v ≤ qual2 β u v
      · simp only [supplierProfit, quantities, revenue, if_neg hd, if_pos hm, if_pos hab, zero_add]
        rw [max_eq_right hab]
        ring
      · simp only [supplierProfit, quantities, revenue, if_neg hd, if_pos hm, if_neg hab, add_zero]
        rw [max_eq_left (le_of_not_ge hab)]
        ring
    · simp [supplierProfit, quantities, revenue, hd, hm]

lemma qualities_pos {β u v : ℝ} (hb : 0 ≤ β) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < qual1 β u v ∧ 0 < qual2 β u v := by
  unfold qual1 qual2
  constructor <;> positivity

lemma native_price_duo {β u v : ℝ} (hb : 0 ≤ β) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hd : (Real.sqrt 3 - 1) * max (qual1 β u v) (qual2 β u v) ≤
      min (qual1 β u v) (qual2 β u v)) : price β u v = rd β u v := by
  obtain ⟨ha, hb'⟩ := qualities_pos hb hu hv
  have he := supplier_duo_least (lt_min ha hb')
    (min_le_max : min (qual1 β u v) (qual2 β u v) ≤ max (qual1 β u v) (qual2 β u v)) hd
  have hs : optimalPrices β u v = {p : ℝ | 0 ≤ p ∧ ∀ q, 0 ≤ q →
      revenue (min (qual1 β u v) (qual2 β u v)) (max (qual1 β u v) (qual2 β u v)) q ≤
      revenue (min (qual1 β u v) (qual2 β u v)) (max (qual1 β u v) (qual2 β u v)) p} := by
    ext p
    simp only [optimalPrices, Set.mem_ofPred_eq, supplierProfit_revenue]
  rw [price, hs, he.csInf_eq, min_add_max]
  unfold rd qual1 qual2
  ring

lemma native_price_mono {β u v : ℝ} (hb : 0 ≤ β) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hd : ¬ (Real.sqrt 3 - 1) * max (qual1 β u v) (qual2 β u v) ≤
      min (qual1 β u v) (qual2 β u v)) :
    price β u v = max (qual1 β u v) (qual2 β u v) / 2 := by
  obtain ⟨ha, hb'⟩ := qualities_pos hb hu hv
  have he := supplier_mono_least (lt_min ha hb')
    (min_le_max : min (qual1 β u v) (qual2 β u v) ≤ max (qual1 β u v) (qual2 β u v)) hd
  have hs : optimalPrices β u v = {p : ℝ | 0 ≤ p ∧ ∀ q, 0 ≤ q →
      revenue (min (qual1 β u v) (qual2 β u v)) (max (qual1 β u v) (qual2 β u v)) q ≤
      revenue (min (qual1 β u v) (qual2 β u v)) (max (qual1 β u v) (qual2 β u v)) p} := by
    ext p
    simp only [optimalPrices, Set.mem_ofPred_eq, supplierProfit_revenue]
  rw [price, hs, he.csInf_eq]

end CrossLicensingProof


namespace CrossLicensingProof
open CrossLicensing.Innovation

lemma duo_sorted_iff {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt 3 - 1) * max a b ≤ min a b ↔
      (Real.sqrt 3 - 1) * b ≤ a ∧ (Real.sqrt 3 - 1) * a ≤ b := by
  obtain ⟨hslo, hshi, hs⟩ := sqrt_three_bounds
  rcases le_total a b with hab | hab
  · rw [max_eq_right hab, min_eq_left hab]
    constructor
    · intro h
      exact ⟨h, by nlinarith [mul_nonneg (show 0 ≤ 2 - Real.sqrt 3 by linarith) ha]⟩
    · exact And.left
  · rw [max_eq_left hab, min_eq_right hab]
    constructor
    · intro h
      exact ⟨by nlinarith [mul_nonneg (show 0 ≤ 2 - Real.sqrt 3 by linarith) hb], h⟩
    · exact And.right

lemma rd_intercepts (β u v : ℝ) : rd β u v = (qual1 β u v + qual2 β u v) / 4 := by
  unfold rd qual1 qual2
  ring

lemma native_duo_quantities {β u v : ℝ} (hb : 0 ≤ β) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hd : (Real.sqrt 3 - 1) * qual2 β u v ≤ qual1 β u v ∧
      (Real.sqrt 3 - 1) * qual1 β u v ≤ qual2 β u v) :
    quantities β u v (price β u v) =
      ((7 * qual1 β u v - 5 * qual2 β u v) / 12,
       (7 * qual2 β u v - 5 * qual1 β u v) / 12) := by
  obtain ⟨ha, hb'⟩ := qualities_pos hb hu hv
  have hd' := (duo_sorted_iff ha.le hb'.le).mpr hd
  rw [native_price_duo hb hu hv hd', rd_intercepts]
  have hh : 0 < max (qual1 β u v) (qual2 β u v) := lt_of_lt_of_le ha (le_max_left _ _)
  obtain ⟨hslo, hshi, hs⟩ := sqrt_three_bounds
  have hx := mul_pos (show 0 < Real.sqrt 3 - 12 / 7 by linarith) hh
  have hid := min_add_max (qual1 β u v) (qual2 β u v)
  have hp : (qual1 β u v + qual2 β u v) / 4 ≤
      2 * min (qual1 β u v) (qual2 β u v) - max (qual1 β u v) (qual2 β u v) := by nlinarith
  simp only [quantities, if_pos hp]
  congr 1 <;> ring

lemma native_duo_gross {β u v : ℝ} (hb : 0 ≤ β) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hd : (Real.sqrt 3 - 1) * qual2 β u v ≤ qual1 β u v ∧
      (Real.sqrt 3 - 1) * qual1 β u v ≤ qual2 β u v) :
    grossProfit1 β u v = duoGross1 β u v ∧ grossProfit2 β u v = duoGross2 β u v := by
  have hq := native_duo_quantities hb hu hv hd
  obtain ⟨ha, hb'⟩ := qualities_pos hb hu hv
  have hp := native_price_duo hb hu hv ((duo_sorted_iff ha.le hb'.le).mpr hd)
  simp only [grossProfit1, grossProfit2, hq]
  rw [hp]
  unfold mfrProfit1 mfrProfit2 duoGross1 duoGross2 rd qual1 qual2
  constructor <;> ring

lemma native_duopoly {β u v : ℝ} (hb : 0 ≤ β) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hd : (Real.sqrt 3 - 1) * qual2 β u v ≤ qual1 β u v ∧
      (Real.sqrt 3 - 1) * qual1 β u v ≤ qual2 β u v) : IsDuopoly β u v := by
  rw [IsDuopoly, native_duo_quantities hb hu hv hd]
  obtain ⟨ha, hb'⟩ := qualities_pos hb hu hv
  obtain ⟨hslo, hshi, hs⟩ := sqrt_three_bounds
  have hx := mul_pos (show 0 < Real.sqrt 3 - 12 / 7 by linarith) ha
  have hy := mul_pos (show 0 < Real.sqrt 3 - 12 / 7 by linarith) hb'
  constructor <;> dsimp <;> nlinarith [hd.1, hd.2]

lemma native_own_mono {β u v : ℝ} (hb : 0 ≤ β) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hd : qual2 β u v < (Real.sqrt 3 - 1) * qual1 β u v) :
    quantities β u v (price β u v) = (qual1 β u v / 4, 0) ∧
    grossProfit1 β u v = (qual1 β u v) ^ 2 / 16 ∧ grossProfit2 β u v = 0 := by
  obtain ⟨ha, hb'⟩ := qualities_pos hb hu hv
  obtain ⟨hslo, hshi, hs⟩ := sqrt_three_bounds
  have hlt : qual2 β u v < qual1 β u v := by
    nlinarith [mul_pos (show 0 < 2 - Real.sqrt 3 by linarith) ha]
  have hn : ¬ (Real.sqrt 3 - 1) * max (qual1 β u v) (qual2 β u v) ≤
      min (qual1 β u v) (qual2 β u v) := by
    rw [max_eq_left hlt.le, min_eq_right hlt.le]
    exact not_le.mpr hd
  have hp := native_price_mono hb hu hv hn
  rw [max_eq_left hlt.le] at hp
  have hh : ¬ qual1 β u v / 2 ≤ 2 * min (qual1 β u v) (qual2 β u v) -
      max (qual1 β u v) (qual2 β u v) := by
    rw [min_eq_right hlt.le, max_eq_left hlt.le]
    nlinarith [mul_pos (show 0 < 7 / 4 - Real.sqrt 3 by linarith) ha]
  have hq : quantities β u v (price β u v) = (qual1 β u v / 4, 0) := by
    rw [hp]
    simp only [quantities, if_neg hh]
    rw [max_eq_left hlt.le]
    simp only [if_pos (show qual1 β u v / 2 ≤ qual1 β u v by linarith), if_neg (not_le.mpr hlt)]
    congr 1
    ring
  refine ⟨hq, ?_, ?_⟩
  · simp only [grossProfit1, hq]
    rw [hp]
    simp only [mfrProfit1]
    unfold qual1
    ring
  · simp only [grossProfit2, hq, mfrProfit2, mul_zero]

end CrossLicensingProof


namespace CrossLicensingProof
open CrossLicensing.Innovation

lemma large_beta_region {β u v : ℝ} (hb : Real.sqrt 3 - 1 ≤ β) (hb1 : β ≤ 1)
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (Real.sqrt 3 - 1) * qual1 β u v ≤ qual2 β u v := by
  obtain ⟨hslo, hshi, hs⟩ := sqrt_three_bounds
  have h1 := mul_nonneg (sub_nonneg.mpr hb) hu
  have hc : 0 ≤ 1 - (Real.sqrt 3 - 1) * β := by nlinarith
  have h2 := mul_nonneg hc hv
  unfold qual1 qual2
  nlinarith

lemma cap_nonneg {β v : ℝ} (hb : 0 ≤ β) (hb' : β < Real.sqrt 3 - 1) (hv : 0 ≤ v) :
    0 < That2 β v := by
  obtain ⟨hslo, hshi, hs⟩ := sqrt_three_bounds
  unfold That2
  apply div_pos
  · have hc : 0 ≤ 1 - β * (Real.sqrt 3 - 1) := by nlinarith
    nlinarith [mul_nonneg hc hv]
  · linarith

lemma cap_ge_other {β v : ℝ} (hb : 0 ≤ β) (hb' : β < Real.sqrt 3 - 1) (hv : 0 ≤ v) :
    v < That2 β v := by
  obtain ⟨hslo, hshi, hs⟩ := sqrt_three_bounds
  unfold That2
  apply (lt_div_iff₀ (show 0 < Real.sqrt 3 - 1 - β by linarith)).mpr
  have hc : 0 < 2 - Real.sqrt 3 := by linarith
  have hx := mul_nonneg (show 0 ≤ (2 - Real.sqrt 3) * (1 + β) by positivity) hv
  nlinarith

lemma region_cap_iff {β u v : ℝ} (hb : β < Real.sqrt 3 - 1) :
    (Real.sqrt 3 - 1) * qual1 β u v ≤ qual2 β u v ↔ u ≤ That2 β v := by
  unfold That2 qual1 qual2
  rw [le_div_iff₀ (show 0 < Real.sqrt 3 - 1 - β by linarith)]
  constructor <;> intro h <;> nlinarith

lemma cap_region {β v : ℝ} (hb : 0 ≤ β) (hb' : β < Real.sqrt 3 - 1) (hv : 0 ≤ v) :
    (Real.sqrt 3 - 1) * qual2 β (That2 β v) v ≤ qual1 β (That2 β v) v ∧
    (Real.sqrt 3 - 1) * qual1 β (That2 β v) v ≤ qual2 β (That2 β v) v := by
  have hc := cap_nonneg hb hb' hv
  have hcv := cap_ge_other hb hb' hv
  have hfirst : qual2 β (That2 β v) v ≤ qual1 β (That2 β v) v := by
    unfold qual1 qual2
    have := mul_nonneg (show 0 ≤ 1 - β by obtain ⟨_, hh, _⟩ := sqrt_three_bounds; linarith) (sub_nonneg.mpr hcv.le)
    nlinarith
  obtain ⟨ha, hbq⟩ := qualities_pos hb hc.le hv
  obtain ⟨hslo, hshi, hs⟩ := sqrt_three_bounds
  refine ⟨?_, (region_cap_iff hb').mpr le_rfl⟩
  nlinarith [mul_nonneg (show 0 ≤ 2 - Real.sqrt 3 by linarith) hbq.le]

lemma mono_implies_small {β u v : ℝ} (hb1 : β ≤ 1) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hm : qual2 β u v < (Real.sqrt 3 - 1) * qual1 β u v) : β < Real.sqrt 3 - 1 := by
  by_contra hn
  exact (not_lt_of_ge (large_beta_region (le_of_not_gt hn) hb1 hu hv)) hm

end CrossLicensingProof


namespace CrossLicensingProof
open CrossLicensing.Innovation

lemma quantities_swap (β u v p : ℝ) :
    quantities β v u p = (quantities β u v p).swap := by
  have ha : qual1 β v u = qual2 β u v := rfl
  have hb : qual2 β v u = qual1 β u v := rfl
  simp only [quantities, ha, hb, min_comm (qual2 β u v), max_comm (qual2 β u v)]
  by_cases hd : p ≤ 2 * min (qual1 β u v) (qual2 β u v) - max (qual1 β u v) (qual2 β u v)
  · simp only [if_pos hd, Prod.swap_prod_mk]
  · simp only [if_neg hd]
    by_cases hm : p ≤ max (qual1 β u v) (qual2 β u v)
    · simp only [if_pos hm]
      by_cases hab : qual1 β u v ≤ qual2 β u v
      · by_cases hba : qual2 β u v ≤ qual1 β u v
        · have he := le_antisymm hab hba
          simp only [he, min_self, max_self] at hd hm
          exfalso
          exact hd (by linarith)
        · simp only [if_pos hab, if_neg hba, Prod.swap_prod_mk]
      · simp only [if_neg hab, if_pos (le_of_not_ge hab), Prod.swap_prod_mk]
    · simp only [if_neg hm, Prod.swap_prod_mk]

lemma supplierProfit_swap (β u v p : ℝ) : supplierProfit β v u p = supplierProfit β u v p := by
  simp only [supplierProfit, quantities_swap β u v p, Prod.fst_swap, Prod.snd_swap]
  ring

lemma price_swap (β u v : ℝ) : price β v u = price β u v := by
  unfold price
  congr 1
  ext p
  simp only [optimalPrices, Set.mem_ofPred_eq, supplierProfit_swap β u v]

lemma grossProfit_swap (β u v : ℝ) : grossProfit1 β v u = grossProfit2 β u v := by
  simp only [grossProfit1, grossProfit2, price_swap β u v, quantities_swap β u v (price β u v), Prod.fst_swap, Prod.snd_swap]
  unfold mfrProfit1 mfrProfit2
  rfl

lemma native_excluded {β u v : ℝ} (hb : 0 ≤ β) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hd : qual1 β u v < (Real.sqrt 3 - 1) * qual2 β u v) : grossProfit1 β u v = 0 := by
  have he := (native_own_mono hb hv hu hd).2.2
  rw [← grossProfit_swap] at he
  exact he

end CrossLicensingProof


namespace CrossLicensingProof
open CrossLicensing.Innovation

lemma quadratic_cost_pos {β k : ℝ} (hb : 0 ≤ β) (hb1 : β ≤ 1) (hk : 49 / 144 < k) :
    0 < 144 * k - (7 - 5 * β) ^ 2 := by
  have h : (7 - 5 * β) ^ 2 ≤ 49 := by nlinarith
  linarith

lemma duo_net_nonneg {β k u v : ℝ} (hu : 0 ≤ u)
    (hd : 0 ≤ 144 * k - (7 - 5 * β) ^ 2) (hs : 0 ≤ slope β k u v) :
    0 ≤ duoGross1 β u v - k * u ^ 2 := by
  have hmul := mul_nonneg hs hu
  have hdu := mul_nonneg hd (sq_nonneg u)
  unfold slope at hmul
  unfold duoGross1
  nlinarith [sq_nonneg (2 - (5 - 7 * β) * v)]

lemma duo_net_max {β k u v x : ℝ} (hd : 0 ≤ 144 * k - (7 - 5 * β) ^ 2)
    (hs : slope β k u v = 0 ∨ (0 ≤ slope β k u v ∧ x ≤ u)) :
    duoGross1 β x v - k * x ^ 2 ≤ duoGross1 β u v - k * u ^ 2 := by
  have hmul : slope β k u v * (x - u) ≤ 0 := by
    rcases hs with hs | ⟨hs, hx⟩
    · rw [hs, zero_mul]
    · exact mul_nonpos_of_nonneg_of_nonpos hs (sub_nonpos.mpr hx)
  have hsq := mul_nonneg hd (sq_nonneg (x - u))
  unfold slope at hmul
  unfold duoGross1
  nlinarith

end CrossLicensingProof


namespace CrossLicensingProof
open CrossLicensing.Innovation

lemma cap_intercepts {β v : ℝ} (hb : β < Real.sqrt 3 - 1) :
    qual2 β (That2 β v) v = (Real.sqrt 3 - 1) * qual1 β (That2 β v) v := by
  have hn : Real.sqrt 3 - 1 - β ≠ 0 := ne_of_gt (by linarith)
  unfold qual1 qual2 That2
  field_simp
  ring

lemma monopoly_vertex_below_cap {β k v : ℝ} (hb : 0 ≤ β)
    (hb' : β < Real.sqrt 3 - 1) (hk : 49 / 144 < k) (hv : 0 ≤ v) :
    1 + β * v < (16 * k - 1) * That2 β v := by
  obtain ⟨hslo, hshi, hs⟩ := sqrt_three_bounds
  have hp : 0 < Real.sqrt 3 - 1 - β := by linarith
  have hu := cap_nonneg hb hb' hv
  have he : (Real.sqrt 3 - 1 - β) * That2 β v =
      2 - Real.sqrt 3 + v * (1 - β * (Real.sqrt 3 - 1)) := by
    unfold That2
    field_simp
  have hr : 0 ≤ Real.sqrt 3 - 1 := by linarith
  have hbr := mul_nonneg (sub_nonneg.mpr hb'.le) hr
  have hc : 0 < 40 / 9 - (49 / 9) * β * (Real.sqrt 3 - 1) + β ^ 2 := by nlinarith [sq_nonneg β]
  have ht := mul_nonneg hc.le hv
  have hconst : 0 < 89 - 49 * Real.sqrt 3 + 9 * β := by nlinarith
  have hsmall : (1 + β * v) * (Real.sqrt 3 - 1 - β) <
      (40 / 9) * (2 - Real.sqrt 3 + v * (1 - β * (Real.sqrt 3 - 1))) := by nlinarith
  have hh : 1 + β * v < (40 / 9) * That2 β v := by
    apply (mul_lt_mul_iff_right₀ hp).mp
    nlinarith [he]
  have hk' : 40 / 9 < 16 * k - 1 := by linarith
  exact hh.trans (mul_lt_mul_of_pos_right hk' hu)

lemma monopoly_net_decreases {β k v x : ℝ} (hb : 0 ≤ β)
    (hb' : β < Real.sqrt 3 - 1) (hk : 49 / 144 < k) (hv : 0 ≤ v)
    (hx : That2 β v < x) :
    (qual1 β x v) ^ 2 / 16 - k * x ^ 2 <
      (qual1 β (That2 β v) v) ^ 2 / 16 - k * (That2 β v) ^ 2 := by
  have he := monopoly_vertex_below_cap hb hb' hk hv
  have hp : 0 < (16 * k - 1) * (x - That2 β v) ^ 2 := by
    apply mul_pos (by linarith)
    exact sq_pos_of_pos (sub_pos.mpr hx)
  have ht := mul_neg_of_neg_of_pos (show 1 + β * v - (16 * k - 1) * That2 β v < 0 by linarith)
    (sub_pos.mpr hx)
  unfold qual1
  nlinarith

lemma monopoly_boundary_jump {β v : ℝ} (hb : 0 ≤ β)
    (hb' : β < Real.sqrt 3 - 1) (hv : 0 ≤ v) :
    (qual1 β (That2 β v) v) ^ 2 / 16 < duoGross1 β (That2 β v) v := by
  have he := cap_intercepts (v := v) hb'
  have ha := (qualities_pos hb (cap_nonneg hb hb' hv).le hv).1
  obtain ⟨hslo, hshi, hs⟩ := sqrt_three_bounds
  have hx := mul_pos (show 0 < 9 - 5 * Real.sqrt 3 by linarith) ha
  have hg : 3 * qual1 β (That2 β v) v <
      7 * qual1 β (That2 β v) v - 5 * qual2 β (That2 β v) v := by nlinarith
  have hy := mul_pos (sub_pos.mpr hg) (show 0 <
      (7 * qual1 β (That2 β v) v - 5 * qual2 β (That2 β v) v) +
      3 * qual1 β (That2 β v) v by linarith)
  have hid : duoGross1 β (That2 β v) v =
      (7 * qual1 β (That2 β v) v - 5 * qual2 β (That2 β v) v) ^ 2 / 144 := by
    unfold duoGross1 qual1 qual2
    ring
  rw [hid]
  nlinarith

end CrossLicensingProof


namespace CrossLicensingProof
open CrossLicensing.Innovation

lemma monopoly_strict_improvement {β k u v : ℝ} (hb : 0 ≤ β) (hb1 : β ≤ 1)
    (hk : 49 / 144 < k) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hm : qual2 β u v < (Real.sqrt 3 - 1) * qual1 β u v) :
    0 ≤ That2 β v ∧
    grossProfit1 β u v - k * u ^ 2 <
      grossProfit1 β (That2 β v) v - k * (That2 β v) ^ 2 := by
  have hsmall := mono_implies_small hb1 hu hv hm
  have hcap := cap_nonneg hb hsmall hv
  have hx : That2 β v < u := by
    by_contra hn
    exact (not_lt_of_ge ((region_cap_iff hsmall).mpr (le_of_not_gt hn))) hm
  have he := (native_own_mono hb hu hv hm).2.1
  have hc := (native_duo_gross hb hcap.le hv (cap_region hb hsmall hv)).1
  refine ⟨hcap.le, ?_⟩
  rw [he, hc]
  exact (monopoly_net_decreases hb hsmall hk hv hx).trans
    (sub_lt_sub_right (monopoly_boundary_jump hb hsmall hv) _)

lemma candidate_best_response {β k u v : ℝ} (hb : 0 ≤ β) (hb1 : β ≤ 1)
    (hk : 49 / 144 < k) (hc : CandidateCertificate β k u v) {x : ℝ} (hx : 0 ≤ x) :
    grossProfit1 β x v - k * x ^ 2 ≤ grossProfit1 β u v - k * u ^ 2 := by
  have hd := (quadratic_cost_pos hb hb1 hk).le
  have hs : 0 ≤ slope β k u v := by
    rcases hc.optimal with he | ⟨_, _, he⟩
    · exact he.ge
    · exact he
  have hg := (native_duo_gross hb hc.own_nonneg hc.other_nonneg ⟨hc.lower, hc.upper⟩).1
  rw [hg]
  by_cases hl : (Real.sqrt 3 - 1) * qual2 β x v ≤ qual1 β x v
  · by_cases hr : (Real.sqrt 3 - 1) * qual1 β x v ≤ qual2 β x v
    · rw [(native_duo_gross hb hx hc.other_nonneg ⟨hl, hr⟩).1]
      apply duo_net_max hd
      rcases hc.optimal with he | ⟨hsmall, he, hs'⟩
      · exact Or.inl he
      · exact Or.inr ⟨hs', he ▸ (region_cap_iff hsmall).mp hr⟩
    · have hm := monopoly_strict_improvement hb hb1 hk hx hc.other_nonneg (lt_of_not_ge hr)
      have hsmall := mono_implies_small hb1 hx hc.other_nonneg (lt_of_not_ge hr)
      have hcap := cap_region hb hsmall hc.other_nonneg
      have hcg := (native_duo_gross hb hm.1 hc.other_nonneg hcap).1
      apply hm.2.le.trans
      rw [hcg]
      apply duo_net_max hd
      rcases hc.optimal with he | ⟨_, he, hs'⟩
      · exact Or.inl he
      · exact Or.inr ⟨hs', he.ge⟩
  · rw [native_excluded hb hx hc.other_nonneg (lt_of_not_ge hl)]
    have hk0 : 0 ≤ k := by linarith
    have hn := duo_net_nonneg hc.own_nonneg hd hs
    nlinarith [mul_nonneg hk0 (sq_nonneg x)]

lemma every_equilibrium_duopoly {β k1 k2 : ℝ} (h : Standing β k1 k2)
    (u v : NNReal) (he : IsInnovationEquilibrium β k1 k2 u v) : IsDuopoly β u v := by
  rcases h with ⟨hb, hb1, hk2, hk12⟩
  have hk1 : 49 / 144 < k1 := hk2.trans hk12
  change (∀ x : NNReal, innovationPayoff1 β k1 x v ≤ innovationPayoff1 β k1 u v) ∧
    (∀ x : NNReal, innovationPayoff2 β k2 u x ≤ innovationPayoff2 β k2 u v) at he
  by_cases hl : (Real.sqrt 3 - 1) * qual2 β u v ≤ qual1 β u v
  · by_cases hr : (Real.sqrt 3 - 1) * qual1 β u v ≤ qual2 β u v
    · exact native_duopoly hb u.property v.property ⟨hl, hr⟩
    · obtain ⟨hc, hi⟩ := monopoly_strict_improvement hb hb1 hk1 u.property v.property (lt_of_not_ge hr)
      have hn := he.1 ⟨That2 β v, hc⟩
      change grossProfit1 β (That2 β v) v - k1 * (That2 β v) ^ 2 ≤
        grossProfit1 β u v - k1 * (u : ℝ) ^ 2 at hn
      exact (not_lt_of_ge hn hi).elim
  · have hm : qual2 β v u < (Real.sqrt 3 - 1) * qual1 β v u := lt_of_not_ge hl
    obtain ⟨hc, hi⟩ := monopoly_strict_improvement hb hb1 hk2 v.property u.property hm
    have hn := he.2 ⟨That2 β u, hc⟩
    change grossProfit2 β u (That2 β u) - k2 * (That2 β u) ^ 2 ≤
      grossProfit2 β u v - k2 * (v : ℝ) ^ 2 at hn
    rw [← grossProfit_swap, ← grossProfit_swap] at hn
    exact (not_lt_of_ge hn hi).elim

lemma certificates_equilibrium {β k1 k2 u v : ℝ} (h : Standing β k1 k2)
    (h1 : CandidateCertificate β k1 u v) (h2 : CandidateCertificate β k2 v u) :
    IsInnovationEquilibrium β k1 k2 ⟨u, h1.own_nonneg⟩ ⟨v, h1.other_nonneg⟩ := by
  rcases h with ⟨hb, hb1, hk2, hk12⟩
  constructor
  · intro x
    exact candidate_best_response hb hb1 (hk2.trans hk12) h1 x.property
  · intro x
    change grossProfit2 β u x - k2 * (x : ℝ) ^ 2 ≤ grossProfit2 β u v - k2 * v ^ 2
    rw [← grossProfit_swap, ← grossProfit_swap]
    exact candidate_best_response hb hb1 hk2 h2 x.property

end CrossLicensingProof


namespace CrossLicensingProof
open CrossLicensing.Innovation

lemma sqrt_three_sq : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)

lemma parameters_sqrt_bounds : (17 : ℝ) / 10 < Real.sqrt 3 ∧ Real.sqrt 3 < 7 / 4 := by
  have h := Real.sqrt_nonneg (3 : ℝ)
  have hs := sqrt_three_sq
  constructor <;> nlinarith

lemma parameters_bounds {β : ℝ} (h0 : 0 ≤ β) (h1 : β ≤ 1) :
    2 ≤ 7 - 5 * β ∧ 7 - 5 * β ≤ 7 ∧ -2 ≤ 5 - 7 * β ∧ 5 - 7 * β ≤ 5 := by
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

lemma cost_coefficient_pos {β k : ℝ} (h0 : 0 ≤ β) (h1 : β ≤ 1)
    (hk : 49 / 144 < k) : 0 < 144 * k - (7 - 5 * β) ^ 2 := by
  obtain ⟨ha0, ha1, _, _⟩ := parameters_bounds h0 h1
  nlinarith

noncomputable def thresholdDen (β k : ℝ) : ℝ :=
  (7 - 4 * Real.sqrt 3) * ((1 - β) * (7 - 5 * β)) +
    48 * (2 * Real.sqrt 3 - 3) * k

lemma thresholdDen_pos {β k : ℝ} (h0 : 0 ≤ β) (h1 : β ≤ 1) (hk : 0 < k) :
    0 < thresholdDen β k := by
  obtain ⟨hs0, hs1⟩ := parameters_sqrt_bounds
  obtain ⟨ha0, _, _, _⟩ := parameters_bounds h0 h1
  have hp : 0 ≤ (1 - β) * (7 - 5 * β) := mul_nonneg (by linarith) (by linarith)
  have hc : 0 ≤ (7 - 4 * Real.sqrt 3) * ((1 - β) * (7 - 5 * β)) :=
    mul_nonneg (by linarith) hp
  unfold thresholdDen
  have hd : 0 < 48 * (2 * Real.sqrt 3 - 3) * k :=
    mul_pos (by linarith) hk
  linarith

lemma khat_normalized (β k : ℝ) :
    khat2 β k = (4 * Real.sqrt 3 - 5) * ((1 - β) * (7 - 5 * β)) * k /
      thresholdDen β k := by
  unfold khat2 thresholdDen
  have hn : -((4 * Real.sqrt 3 - 5) * (β - 1) * (5 * β - 7) * k) =
      -((4 * Real.sqrt 3 - 5) * ((1 - β) * (7 - 5 * β)) * k) := by ring
  have hd : (4 * Real.sqrt 3 - 7) * (β - 1) * (5 * β - 7) +
      48 * (3 - 2 * Real.sqrt 3) * k =
      -((7 - 4 * Real.sqrt 3) * ((1 - β) * (7 - 5 * β)) +
      48 * (2 * Real.sqrt 3 - 3) * k) := by ring
  rw [hn, hd, neg_div_neg_eq]

end CrossLicensingProof


namespace CrossLicensingProof
open CrossLicensing.Innovation

lemma khat_mul_den {β k : ℝ} (hd : thresholdDen β k ≠ 0) :
    khat2 β k * thresholdDen β k =
      (4 * Real.sqrt 3 - 5) * ((1 - β) * (7 - 5 * β)) * k := by
  rw [khat_normalized, div_mul_cancel₀ _ hd]

lemma threshold_differences {β k : ℝ} (hd : thresholdDen β k ≠ 0) :
    (khat2 β k - k) * thresholdDen β k =
      48 * (2 * Real.sqrt 3 - 3) * k * ((1 - β) * (7 - 5 * β) / 12 - k) ∧
    (khat2 β k - (1 - β) * (7 - 5 * β) / 12) * thresholdDen β k =
      (7 - 4 * Real.sqrt 3) * ((1 - β) * (7 - 5 * β)) *
        (k - (1 - β) * (7 - 5 * β) / 12) := by
  have he := khat_mul_den hd
  constructor <;> rw [sub_mul, he] <;> unfold thresholdDen <;> ring

lemma interior_critical_bounds {β k1 k2 : ℝ} (h : Standing β k1 k2)
    (hi : khat2 β k1 ≤ k2) :
    (1 - β) * (7 - 5 * β) / 12 < k1 ∧
      (1 - β) * (7 - 5 * β) / 12 < k2 := by
  obtain ⟨h0, h1, hk2, h21⟩ := h
  have hk1 : 0 < k1 := by linarith
  have hd := thresholdDen_pos h0 h1 hk1
  obtain ⟨he1, he2⟩ := threshold_differences (ne_of_gt hd)
  obtain ⟨hs0, hs1⟩ := parameters_sqrt_bounds
  have hc : 0 < 48 * (2 * Real.sqrt 3 - 3) * k1 :=
    mul_pos (by linarith) hk1
  have hdiff : (khat2 β k1 - k1) * thresholdDen β k1 < 0 :=
    mul_neg_of_neg_of_pos (by linarith) hd
  have hkcrit : (1 - β) * (7 - 5 * β) / 12 < k1 := by
    by_contra hn
    have : 0 ≤ 48 * (2 * Real.sqrt 3 - 3) * k1 *
        ((1 - β) * (7 - 5 * β) / 12 - k1) :=
      mul_nonneg hc.le (by linarith)
    linarith
  refine ⟨hkcrit, ?_⟩
  by_cases hb : β = 1
  · subst β
    norm_num
    linarith
  · have hp : 0 < (1 - β) * (7 - 5 * β) :=
      mul_pos (by have : β < 1 := lt_of_le_of_ne h1 hb; linarith) (by linarith)
    have hpos : 0 < (7 - 4 * Real.sqrt 3) * ((1 - β) * (7 - 5 * β)) *
        (k1 - (1 - β) * (7 - 5 * β) / 12) :=
      mul_pos (mul_pos (by linarith) hp) (by linarith)
    have : (1 - β) * (7 - 5 * β) / 12 < khat2 β k1 := by
      nlinarith
    linarith

lemma interior_diagonal_bounds {β k1 k2 : ℝ} (h : Standing β k1 k2)
    (hi : khat2 β k1 ≤ k2) :
    (7 - 5 * β) * (5 - 7 * β) < 144 * k1 - (7 - 5 * β)^2 ∧
    (7 - 5 * β) * (5 - 7 * β) < 144 * k2 - (7 - 5 * β)^2 := by
  obtain ⟨h1, h2⟩ := interior_critical_bounds h hi
  constructor <;> nlinarith

end CrossLicensingProof


namespace CrossLicensingProof
open CrossLicensing.Innovation

noncomputable def interiorDet (β k1 k2 : ℝ) : ℝ :=
  (144*k1-(7-5*β)^2)*(144*k2-(7-5*β)^2)-(7-5*β)^2*(5-7*β)^2

lemma interiorDet_pos {β k1 k2 : ℝ} (h : Standing β k1 k2)
    (hi : khat2 β k1 ≤ k2) : 0 < interiorDet β k1 k2 := by
  obtain ⟨h0, h1, hk2, h21⟩ := h
  have hd1 := cost_coefficient_pos h0 h1 (lt_trans hk2 h21)
  have hd2 := cost_coefficient_pos h0 h1 hk2
  obtain ⟨he1, he2⟩ := interior_diagonal_bounds ⟨h0,h1,hk2,h21⟩ hi
  obtain ⟨ha0, ha1, hb0, hb1⟩ := parameters_bounds h0 h1
  by_cases hb : 0 ≤ 5-7*β
  · have hab : 0 ≤ (7-5*β)*(5-7*β) := mul_nonneg (by linarith) hb
    have hm := mul_pos (sub_pos.mpr he1) (sub_pos.mpr he2)
    have hm2 := mul_nonneg hab (sub_nonneg.mpr he1.le)
    have hm3 := mul_nonneg hab (sub_nonneg.mpr he2.le)
    unfold interiorDet
    nlinarith
  · have hβ : 5/7 < β := by linarith
    have ha : 7-5*β < 24/7 := by linarith
    have hsmall : (7-5*β)^2-(7-5*β)*(5-7*β) < 49 := by
      nlinarith [sq_nonneg (β-5/7)]
    have ht1 : -(7-5*β)*(5-7*β) < 144*k1-(7-5*β)^2 := by linarith
    have ht2 : -(7-5*β)*(5-7*β) < 144*k2-(7-5*β)^2 := by linarith
    have hp : 0 ≤ -(7-5*β)*(5-7*β) := by
      nlinarith [mul_nonneg (show 0 ≤ 7-5*β by linarith) (show 0 ≤ -(5-7*β) by linarith)]
    have hm := mul_pos (sub_pos.mpr ht1) (sub_pos.mpr ht2)
    have hm2 := mul_nonneg hp (sub_nonneg.mpr ht1.le)
    have hm3 := mul_nonneg hp (sub_nonneg.mpr ht2.le)
    unfold interiorDet
    nlinarith

lemma TI1_normalized {β k1 k2 : ℝ} (hd : interiorDet β k1 k2 ≠ 0) :
    TI1 β k1 k2 = 2*(7-5*β)*(144*k2-(7-5*β)^2-(7-5*β)*(5-7*β)) /
      interiorDet β k1 k2 := by
  have he : 6*k2*((7-5*β)^2-144*k1)+(7-5*β)^2*(β^2+6*k1-1) =
      -(interiorDet β k1 k2)/24 := by unfold interiorDet; ring
  unfold TI1
  rw [he]
  field_simp [hd]
  ring

lemma TI2_normalized {β k1 k2 : ℝ} (hd : interiorDet β k1 k2 ≠ 0) :
    TI2 β k1 k2 = 2*(7-5*β)*(144*k1-(7-5*β)^2-(7-5*β)*(5-7*β)) /
      interiorDet β k1 k2 := by
  have he : 6*k1*((7-5*β)^2-144*k2)+(7-5*β)^2*(β^2+6*k2-1) =
      -(interiorDet β k1 k2)/24 := by unfold interiorDet; ring
  unfold TI2
  rw [he]
  field_simp [hd]
  ring

lemma interior_candidate_algebra {β k1 k2 : ℝ} (h : Standing β k1 k2)
    (hi : khat2 β k1 ≤ k2) :
    0 < TI1 β k1 k2 ∧ TI1 β k1 k2 < TI2 β k1 k2 ∧
    slope β k1 (TI1 β k1 k2) (TI2 β k1 k2) = 0 ∧
    slope β k2 (TI2 β k1 k2) (TI1 β k1 k2) = 0 := by
  have hd := interiorDet_pos h hi
  obtain ⟨he1, he2⟩ := interior_diagonal_bounds h hi
  obtain ⟨ha, _, _, _⟩ := parameters_bounds h.1 h.2.1
  rw [TI1_normalized (ne_of_gt hd), TI2_normalized (ne_of_gt hd)]
  refine ⟨div_pos (mul_pos (by linarith) (by linarith)) hd, ?_, ?_, ?_⟩
  · apply (div_lt_div_iff_of_pos_right hd).2
    nlinarith [h.2.2.2]
  · unfold slope
    field_simp [ne_of_gt hd]
    unfold interiorDet
    ring
  · unfold slope
    field_simp [ne_of_gt hd]
    unfold interiorDet
    ring

end CrossLicensingProof


namespace CrossLicensingProof
open CrossLicensing.Innovation

lemma boundary_beta_small {β k1 k2 : ℝ} (h : Standing β k1 k2)
    (hb : k2 < khat2 β k1) : β < 1/3 := by
  obtain ⟨h0,h1,hk2,h21⟩ := h
  have hk1 : 0 < k1 := by linarith
  have hd := thresholdDen_pos h0 h1 hk1
  have he := khat_mul_den (ne_of_gt hd)
  obtain ⟨hs0,hs1⟩ := parameters_sqrt_bounds
  obtain ⟨ha,_,_,_⟩ := parameters_bounds h0 h1
  by_contra hn
  have hβ : 1/3 ≤ β := le_of_not_gt hn
  have hp : (1-β)*(7-5*β) ≤ 32/9 := by nlinarith
  have hp0 : 0 ≤ (1-β)*(7-5*β) := mul_nonneg (by linarith) (by linarith)
  have he0 : 0 ≤ 4*Real.sqrt 3-5 := by linarith
  have hbound : (4*Real.sqrt 3-5)*((1-β)*(7-5*β)) <
      (49/144)*(48*(2*Real.sqrt 3-3)) := by
    nlinarith [mul_nonneg he0 (sub_nonneg.mpr hp)]
  have hm := mul_lt_mul_of_pos_right hbound hk1
  have hc : 0 ≤ (7-4*Real.sqrt 3)*((1-β)*(7-5*β)) :=
    mul_nonneg (by linarith) hp0
  have hden : 48*(2*Real.sqrt 3-3)*k1 ≤ thresholdDen β k1 := by
    unfold thresholdDen
    linarith
  have hK : khat2 β k1 < 49/144 := by nlinarith
  linarith

noncomputable def boundaryA (β : ℝ) : ℝ := (2-Real.sqrt 3)/(Real.sqrt 3-1-β)
noncomputable def boundaryB (β : ℝ) : ℝ := (1-β*(Real.sqrt 3-1))/(Real.sqrt 3-1-β)

lemma boundary_parameters {β : ℝ} (h0 : 0 ≤ β) (hβ : β < 1/3) :
    β < Real.sqrt 3-1 ∧ 0 < boundaryA β ∧ 1 < boundaryB β ∧
    0 < 2-(5-7*β)*boundaryA β := by
  obtain ⟨hs0,hs1⟩ := parameters_sqrt_bounds
  have hs := sqrt_three_sq
  have hd : 0 < Real.sqrt 3-1-β := by linarith
  refine ⟨by linarith, div_pos (by linarith) hd, ?_, ?_⟩
  · unfold boundaryB
    apply (lt_div_iff₀ hd).2
    nlinarith
  · have he : (2-(5-7*β)*boundaryA β)*(Real.sqrt 3-1-β) =
        (7*Real.sqrt 3-12)*(1-β) := by
      unfold boundaryA
      field_simp
      ring
    have ht : 0 < (7*Real.sqrt 3-12)*(1-β) := by
      apply mul_pos
      · nlinarith
      · linarith
    nlinarith

lemma That2_affine (β u : ℝ) : That2 β u = boundaryA β + boundaryB β*u := by
  unfold That2 boundaryA boundaryB
  ring

end CrossLicensingProof


namespace CrossLicensingProof
open CrossLicensing.Innovation

lemma TBden_pos {β k : ℝ} (h0 : 0 ≤ β) (hβ : β < 1/3) (hk : 49/144 < k) :
    0 < TBden β k := by
  obtain ⟨hc,hA,hB,hn⟩ := boundary_parameters h0 hβ
  have hd := cost_coefficient_pos h0 (by linarith) hk
  have hden : 0 < Real.sqrt 3-1-β := by linarith
  have ha : 0 < 7-5*β := by linarith
  have hb : 0 < 5-7*β := by linarith
  have hQ : 0 < (144*k-(7-5*β)^2)+(7-5*β)*(5-7*β)*boundaryB β :=
    add_pos hd (mul_pos (mul_pos ha hb) (by linarith))
  have he : ((144*k-(7-5*β)^2)+(7-5*β)*(5-7*β)*boundaryB β)*
      (Real.sqrt 3-1-β) = Real.sqrt 3*TBden β k := by
    unfold boundaryB TBden
    field_simp [ne_of_gt hden]
    ring_nf
    simp only [sqrt_three_sq]
    ring
  have hmul := mul_pos hQ hden
  have hs := Real.sqrt_nonneg (3 : ℝ)
  nlinarith

lemma boundary_equations {β k : ℝ} (hd : TBden β k ≠ 0) :
    (144*k-(7-5*β)^2)*TB1 β k+(7-5*β)*(5-7*β)*TB2 β k = 2*(7-5*β) ∧
    (Real.sqrt 3-1-β)*TB2 β k =
      2-Real.sqrt 3+(1-β*(Real.sqrt 3-1))*TB1 β k := by
  constructor <;> unfold TB1 TB2 <;> field_simp [hd] <;> unfold TBden <;>
    ring_nf
  rw [sqrt_three_sq]
  ring

lemma boundary_candidate_algebra {β k : ℝ} (h0 : 0 ≤ β) (hβ : β < 1/3)
    (hk : 49/144 < k) :
    0 < TB1 β k ∧ TB1 β k < TB2 β k ∧
    TB2 β k = That2 β (TB1 β k) ∧ slope β k (TB1 β k) (TB2 β k) = 0 := by
  have hd := TBden_pos h0 hβ hk
  obtain ⟨he1,he2⟩ := boundary_equations (ne_of_gt hd)
  obtain ⟨hc,hA,hB,hn⟩ := boundary_parameters h0 hβ
  have he : TB2 β k = That2 β (TB1 β k) := by
    unfold That2
    apply (eq_div_iff (by linarith : Real.sqrt 3-1-β ≠ 0)).2
    nlinarith [he2]
  have hu : 0 < TB1 β k := by
    unfold TB1
    apply div_pos _ hd
    obtain ⟨hs0,hs1⟩ := parameters_sqrt_bounds
    have hneg : (4*Real.sqrt 3-7)*(β-1)*(5*β-7) < 0 :=
      mul_neg_of_pos_of_neg
        (mul_pos_of_neg_of_neg (by linarith) (by linarith)) (by linarith)
    nlinarith
  refine ⟨hu, ?_, he, ?_⟩
  · rw [he, That2_affine]
    nlinarith [mul_pos (sub_pos.mpr hB) hu]
  · unfold slope
    nlinarith [he1]

end CrossLicensingProof


namespace CrossLicensingProof
open CrossLicensing.Innovation

lemma ordered_qualities {β u v : ℝ} (h0 : 0 ≤ β) (h1 : β ≤ 1)
    (hu : 0 ≤ u) (huv : u ≤ v) :
    0 < qual1 β u v ∧ qual1 β u v ≤ qual2 β u v := by
  have hv : 0 ≤ v := le_trans hu huv
  have hp := mul_nonneg h0 hv
  have ho := mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr huv)
  unfold qual1 qual2
  constructor <;> nlinarith

lemma region_of_cap {β u v : ℝ} (h0 : 0 ≤ β) (h1 : β ≤ 1)
    (hu : 0 ≤ u) (huv : u ≤ v) (hc : β < Real.sqrt 3-1)
    (hcap : v ≤ boundaryA β + boundaryB β*u) :
    (Real.sqrt 3-1)*qual2 β u v ≤ qual1 β u v ∧
    (Real.sqrt 3-1)*qual1 β u v ≤ qual2 β u v := by
  obtain ⟨hq,ho⟩ := ordered_qualities h0 h1 hu huv
  obtain ⟨hs0,hs1⟩ := parameters_sqrt_bounds
  have hd : 0 < Real.sqrt 3-1-β := by linarith
  have he : boundaryA β+boundaryB β*u =
      (2-Real.sqrt 3+(1-β*(Real.sqrt 3-1))*u)/(Real.sqrt 3-1-β) := by
    unfold boundaryA boundaryB
    ring
  rw [he] at hcap
  have hm := (le_div_iff₀ hd).mp hcap
  constructor
  · unfold qual1 qual2
    nlinarith
  · nlinarith [mul_nonneg (show 0 ≤ 2-Real.sqrt 3 by linarith) hq.le]

lemma region_large_beta {β u v : ℝ} (hc : Real.sqrt 3-1 ≤ β)
    (h1 : β ≤ 1) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (Real.sqrt 3-1)*qual2 β u v ≤ qual1 β u v ∧
    (Real.sqrt 3-1)*qual1 β u v ≤ qual2 β u v := by
  obtain ⟨hs0,hs1⟩ := parameters_sqrt_bounds
  have hs := sqrt_three_sq
  have hcoef : 0 ≤ 1-(Real.sqrt 3-1)*β := by nlinarith
  have hu1 := mul_nonneg hcoef hu
  have hv1 := mul_nonneg hcoef hv
  have hu2 := mul_nonneg (sub_nonneg.mpr hc) hu
  have hv2 := mul_nonneg (sub_nonneg.mpr hc) hv
  unfold qual1 qual2
  constructor <;> nlinarith

end CrossLicensingProof


namespace CrossLicensingProof
open CrossLicensing.Innovation

lemma boundary_threshold_equation {β k : ℝ} (hd : TBden β k ≠ 0)
    (he : thresholdDen β k ≠ 0) :
    (144*khat2 β k-(7-5*β)^2)*TB2 β k =
      (7-5*β)*(2-(5-7*β)*TB1 β k) := by
  rw [khat_normalized]
  unfold TB1 TB2
  field_simp [hd, he]
  unfold TBden thresholdDen
  ring_nf

lemma boundary_certificates {β k1 k2 : ℝ} (h : Standing β k1 k2)
    (hb : k2 < khat2 β k1) :
    CandidateCertificate β k1 (TB1 β k1) (TB2 β k1) ∧
    CandidateCertificate β k2 (TB2 β k1) (TB1 β k1) := by
  have hs := boundary_beta_small h hb
  have hk : 49/144 < k1 := lt_trans h.2.2.1 h.2.2.2
  obtain ⟨hu,huv,he,hslope⟩ := boundary_candidate_algebra h.1 hs hk
  have hv : 0 < TB2 β k1 := lt_trans hu huv
  obtain ⟨hc,_,_,_⟩ := boundary_parameters h.1 hs
  obtain ⟨hl,hr⟩ := region_of_cap h.1 h.2.1 hu.le huv.le hc
    (by rw [he, That2_affine])
  have hden := TBden_pos h.1 hs hk
  have hden2 := thresholdDen_pos (k := k1) h.1 h.2.1 (by linarith)
  have heq := boundary_threshold_equation (ne_of_gt hden) (ne_of_gt hden2)
  have hsl : 0 ≤ slope β k2 (TB2 β k1) (TB1 β k1) := by
    unfold slope
    nlinarith [mul_pos (sub_pos.mpr hb) hv]
  refine ⟨⟨hu.le,hv.le,hl,hr,Or.inl hslope⟩, ?_⟩
  refine ⟨hv.le,hu.le,?_,?_,Or.inr ⟨hc,he,hsl⟩⟩
  · simpa only [qual1,qual2,add_comm,add_left_comm,add_assoc] using hr
  · simpa only [qual1,qual2,add_comm,add_left_comm,add_assoc] using hl

end CrossLicensingProof


namespace CrossLicensingProof
open CrossLicensing.Innovation

lemma interior_small_cap {β k1 k2 : ℝ} (h : Standing β k1 k2)
    (hi : khat2 β k1 ≤ k2) (hβ : β < 1/3) :
    TI2 β k1 k2 ≤ boundaryA β + boundaryB β * TI1 β k1 k2 := by
  have hk : 49/144 < k1 := lt_trans h.2.2.1 h.2.2.2
  have hd1 := cost_coefficient_pos h.1 h.2.1 hk
  have hdet := interiorDet_pos h hi
  obtain ⟨_,_,hsi,hsj⟩ := interior_candidate_algebra h hi
  obtain ⟨hu,huv,hcap,hsb⟩ := boundary_candidate_algebra h.1 hβ hk
  have hv : 0 < TB2 β k1 := lt_trans hu huv
  have hden := TBden_pos h.1 hβ hk
  have hden2 := thresholdDen_pos (k := k1) h.1 h.2.1 (by linarith)
  have htb := boundary_threshold_equation (ne_of_gt hden) (ne_of_gt hden2)
  have hrel : interiorDet β k1 k2 * (TI2 β k1 k2-TB2 β k1) =
      -144*(k2-khat2 β k1)*(TB2 β k1)*(144*k1-(7-5*β)^2) := by
    unfold slope at hsi hsj hsb
    unfold interiorDet
    linear_combination
      (7-5*β)*(5-7*β)*hsi - (144*k1-(7-5*β)^2)*hsj -
      (7-5*β)*(5-7*β)*hsb - (144*k1-(7-5*β)^2)*htb
  have hrhs : 0 ≤ 144*(k2-khat2 β k1)*(TB2 β k1)*(144*k1-(7-5*β)^2) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hi)) hv.le) hd1.le
  have hvle : TI2 β k1 k2 ≤ TB2 β k1 := by nlinarith
  have hab : 0 ≤ (7-5*β)*(5-7*β) := mul_nonneg (by linarith [h.2.1]) (by linarith)
  have hprod := mul_nonneg hab (sub_nonneg.mpr hvle)
  have hule : TB1 β k1 ≤ TI1 β k1 k2 := by
    unfold slope at hsi hsb
    nlinarith
  obtain ⟨_,_,hB,_⟩ := boundary_parameters h.1 hβ
  rw [That2_affine] at hcap
  have hmul := mul_le_mul_of_nonneg_left hule (by linarith : 0 ≤ boundaryB β)
  linarith

end CrossLicensingProof


namespace CrossLicensingProof
open CrossLicensing.Innovation

lemma interior_medium_small {β k1 k2 : ℝ} (h : Standing β k1 k2)
    (hi : khat2 β k1 ≤ k2) (hβ : 1/3 ≤ β) : TI2 β k1 k2 < 2/3 := by
  obtain ⟨hu,huv,_,hsj⟩ := interior_candidate_algebra h hi
  have hv : 0 < TI2 β k1 k2 := lt_trans hu huv
  obtain ⟨ha,ha7,hb2,_⟩ := parameters_bounds h.1 h.2.1
  have hk := h.2.2.1
  unfold slope at hsj
  by_cases hb : 0 ≤ 5-7*β
  · have hamax : 7-5*β ≤ 16/3 := by linarith
    have hd : 3*(7-5*β) < 144*k2-(7-5*β)^2 := by nlinarith
    have habu := mul_nonneg (mul_nonneg (show 0 ≤ 7-5*β by linarith) hb) hu.le
    have hmul := mul_pos (sub_pos.mpr hd) hv
    nlinarith
  · have hamax : 7-5*β < 24/7 := by linarith
    have hab : (7-5*β)*(5-7*β) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    have hablower := mul_nonneg (show 0 ≤ 7-5*β by linarith) (show 0 ≤ 5-7*β+2 by linarith)
    have hd : 3*(7-5*β) < 144*k2-(7-5*β)^2+(7-5*β)*(5-7*β) := by
      nlinarith
    have hprod := mul_nonpos_of_nonpos_of_nonneg hab (sub_nonneg.mpr huv.le)
    have hmul := mul_pos (sub_pos.mpr hd) hv
    nlinarith

lemma boundaryA_gt_two_thirds {β : ℝ} (hβ : 1/3 ≤ β)
    (hc : β < Real.sqrt 3-1) : 2/3 < boundaryA β := by
  have hs := sqrt_three_sq
  have hn := Real.sqrt_nonneg (3 : ℝ)
  have hd : 0 < Real.sqrt 3-1-β := by linarith
  unfold boundaryA
  apply (lt_div_iff₀ hd).2
  nlinarith

lemma interior_regions {β k1 k2 : ℝ} (h : Standing β k1 k2)
    (hi : khat2 β k1 ≤ k2) :
    (Real.sqrt 3-1)*qual2 β (TI1 β k1 k2) (TI2 β k1 k2) ≤
      qual1 β (TI1 β k1 k2) (TI2 β k1 k2) ∧
    (Real.sqrt 3-1)*qual1 β (TI1 β k1 k2) (TI2 β k1 k2) ≤
      qual2 β (TI1 β k1 k2) (TI2 β k1 k2) := by
  obtain ⟨hu,huv,_,_⟩ := interior_candidate_algebra h hi
  by_cases hc : β < Real.sqrt 3-1
  · apply region_of_cap h.1 h.2.1 hu.le huv.le hc
    by_cases hb : β < 1/3
    · exact interior_small_cap h hi hb
    · have hb' : 1/3 ≤ β := le_of_not_gt hb
      have hv := interior_medium_small h hi hb'
      have hA := boundaryA_gt_two_thirds hb' hc
      obtain ⟨hs0,hs1⟩ := parameters_sqrt_bounds
      have hnum : 0 < 1-β*(Real.sqrt 3-1) := by nlinarith [h.2.1]
      have hB : 0 < boundaryB β := div_pos hnum (by linarith)
      have hmul := mul_pos hB hu
      linarith
  · exact region_large_beta (le_of_not_gt hc) h.2.1 hu.le (lt_trans hu huv).le

lemma interior_certificates {β k1 k2 : ℝ} (h : Standing β k1 k2)
    (hi : khat2 β k1 ≤ k2) :
    CandidateCertificate β k1 (TI1 β k1 k2) (TI2 β k1 k2) ∧
    CandidateCertificate β k2 (TI2 β k1 k2) (TI1 β k1 k2) := by
  obtain ⟨hu,huv,h1,h2⟩ := interior_candidate_algebra h hi
  obtain ⟨hl,hr⟩ := interior_regions h hi
  have hv := lt_trans hu huv
  refine ⟨⟨hu.le,hv.le,hl,hr,Or.inl h1⟩, ?_⟩
  refine ⟨hv.le,hu.le,?_,?_,Or.inl h2⟩
  · simpa only [qual1,qual2,add_comm,add_left_comm,add_assoc] using hr
  · simpa only [qual1,qual2,add_comm,add_left_comm,add_assoc] using hl

end CrossLicensingProof


namespace CrossLicensingProof
open CrossLicensing.Innovation

lemma candidate_certificates {β k1 k2 : ℝ} (h : Standing β k1 k2) :
    CandidateCertificate β k1 (Tstar1 β k1 k2) (Tstar2 β k1 k2) ∧
    CandidateCertificate β k2 (Tstar2 β k1 k2) (Tstar1 β k1 k2) := by
  by_cases hb : k2 < khat2 β k1
  · simpa only [Tstar1,Tstar2,if_pos hb] using boundary_certificates h hb
  · simpa only [Tstar1,Tstar2,if_neg hb] using interior_certificates h (le_of_not_gt hb)

lemma boundary_branch {β k1 k2 : ℝ} (h : Standing β k1 k2)
    (hb : k2 < khat2 β k1) :
    β < Real.sqrt 3-1 ∧ Tstar1 β k1 k2 = TB1 β k1 ∧
    Tstar2 β k1 k2 = TB2 β k1 ∧
    Tstar2 β k1 k2 = That2 β (Tstar1 β k1 k2) := by
  have hs := boundary_beta_small h hb
  obtain ⟨hc,_,_,_⟩ := boundary_parameters h.1 hs
  obtain ⟨_,_,he,_⟩ := boundary_candidate_algebra h.1 hs (lt_trans h.2.2.1 h.2.2.2)
  simp only [Tstar1,Tstar2,if_pos hb]
  exact ⟨hc, trivial, trivial, he⟩

lemma duo_payoff_derivative (β k u v : ℝ) :
    HasDerivAt (fun x => duoGross1 β x v-k*x^2) (slope β k u v / 72) u := by
  have hd := (((((hasDerivAt_id u).const_mul (5*β-7)).add_const
    ((5-7*β)*v-2)).pow 2).div_const 144).sub (((hasDerivAt_id u).pow 2).const_mul k)
  convert hd using 1 <;> try rfl
  · funext x
    dsimp [duoGross1]
    ring
  · dsimp [slope]
    ring

lemma interior_branch {β k1 k2 : ℝ} (h : Standing β k1 k2)
    (hi : khat2 β k1 ≤ k2) :
    Tstar1 β k1 k2 = TI1 β k1 k2 ∧ Tstar2 β k1 k2 = TI2 β k1 k2 ∧
    HasDerivAt (fun x => duoGross1 β x (Tstar2 β k1 k2)-k1*x^2) 0 (Tstar1 β k1 k2) ∧
    HasDerivAt (fun x => duoGross2 β (Tstar1 β k1 k2) x-k2*x^2) 0 (Tstar2 β k1 k2) := by
  have hn := not_lt.mpr hi
  simp only [Tstar1,Tstar2,if_neg hn]
  obtain ⟨_,_,h1,h2⟩ := interior_candidate_algebra h hi
  refine ⟨trivial, trivial, ?_, ?_⟩
  · simpa only [h1,zero_div] using duo_payoff_derivative β k1 (TI1 β k1 k2) (TI2 β k1 k2)
  · simpa only [duoGross1,duoGross2,h2,zero_div] using
      duo_payoff_derivative β k2 (TI2 β k1 k2) (TI1 β k1 k2)

end CrossLicensingProof


namespace CrossLicensingProof
open CrossLicensing.Innovation

theorem full_native_result (β k1 k2 : ℝ) (h : Standing β k1 k2) :
    (∀ T1 T2 : NNReal, IsInnovationEquilibrium β k1 k2 T1 T2 → IsDuopoly β T1 T2) ∧
    (∃ T1 T2 : NNReal, (T1 : ℝ) = Tstar1 β k1 k2 ∧ (T2 : ℝ) = Tstar2 β k1 k2 ∧
      IsInnovationEquilibrium β k1 k2 T1 T2) ∧
    IsDuopoly β (Tstar1 β k1 k2) (Tstar2 β k1 k2) ∧
    (k2 < khat2 β k1 →
      β < Real.sqrt 3 - 1 ∧ Tstar1 β k1 k2 = TB1 β k1 ∧ Tstar2 β k1 k2 = TB2 β k1 ∧
      Tstar2 β k1 k2 = That2 β (Tstar1 β k1 k2)) ∧
    (khat2 β k1 ≤ k2 →
      Tstar1 β k1 k2 = TI1 β k1 k2 ∧ Tstar2 β k1 k2 = TI2 β k1 k2 ∧
      HasDerivAt (fun x => duoGross1 β x (Tstar2 β k1 k2) - k1 * x ^ 2) 0 (Tstar1 β k1 k2) ∧
      HasDerivAt (fun x => duoGross2 β (Tstar1 β k1 k2) x - k2 * x ^ 2) 0 (Tstar2 β k1 k2))  := by
  obtain ⟨h1, h2⟩ := candidate_certificates h
  refine ⟨every_equilibrium_duopoly h, ?_, ?_, boundary_branch h, interior_branch h⟩
  · refine ⟨⟨Tstar1 β k1 k2, h1.own_nonneg⟩, ⟨Tstar2 β k1 k2, h1.other_nonneg⟩,
      rfl, rfl, ?_⟩
    exact certificates_equilibrium h h1 h2
  · exact native_duopoly h.1 h1.own_nonneg h1.other_nonneg ⟨h1.lower, h1.upper⟩

end CrossLicensingProof


open CrossLicensing.Innovation

namespace CrossLicensing.Innovation

theorem proposition_2 (β k1 k2 : ℝ) (h : Standing β k1 k2) :
    (∀ T1 T2 : NNReal, IsInnovationEquilibrium β k1 k2 T1 T2 → IsDuopoly β T1 T2) ∧
    (∃ T1 T2 : NNReal, (T1 : ℝ) = Tstar1 β k1 k2 ∧ (T2 : ℝ) = Tstar2 β k1 k2 ∧
      IsInnovationEquilibrium β k1 k2 T1 T2) ∧
    IsDuopoly β (Tstar1 β k1 k2) (Tstar2 β k1 k2) ∧
    (k2 < khat2 β k1 →
      β < Real.sqrt 3 - 1 ∧ Tstar1 β k1 k2 = TB1 β k1 ∧ Tstar2 β k1 k2 = TB2 β k1 ∧
      Tstar2 β k1 k2 = That2 β (Tstar1 β k1 k2)) ∧
    (khat2 β k1 ≤ k2 →
      Tstar1 β k1 k2 = TI1 β k1 k2 ∧ Tstar2 β k1 k2 = TI2 β k1 k2 ∧
      HasDerivAt (fun x => duoGross1 β x (Tstar2 β k1 k2) - k1 * x ^ 2) 0 (Tstar1 β k1 k2) ∧
      HasDerivAt (fun x => duoGross2 β (Tstar1 β k1 k2) x - k2 * x ^ 2) 0 (Tstar2 β k1 k2)) := by
  exact CrossLicensingProof.full_native_result β k1 k2 h

end CrossLicensing.Innovation

open CrossLicensing.Innovation

theorem solution (β k1 k2 : ℝ) (h : Standing β k1 k2) :
    (∀ T1 T2 : NNReal, IsInnovationEquilibrium β k1 k2 T1 T2 → IsDuopoly β T1 T2) ∧
    (∃ T1 T2 : NNReal, (T1 : ℝ) = Tstar1 β k1 k2 ∧ (T2 : ℝ) = Tstar2 β k1 k2 ∧
      IsInnovationEquilibrium β k1 k2 T1 T2) ∧
    IsDuopoly β (Tstar1 β k1 k2) (Tstar2 β k1 k2) ∧
    (k2 < khat2 β k1 →
      β < Real.sqrt 3 - 1 ∧ Tstar1 β k1 k2 = TB1 β k1 ∧ Tstar2 β k1 k2 = TB2 β k1 ∧
      Tstar2 β k1 k2 = That2 β (Tstar1 β k1 k2)) ∧
    (khat2 β k1 ≤ k2 →
      Tstar1 β k1 k2 = TI1 β k1 k2 ∧ Tstar2 β k1 k2 = TI2 β k1 k2 ∧
      HasDerivAt (fun x => duoGross1 β x (Tstar2 β k1 k2) - k1 * x ^ 2) 0 (Tstar1 β k1 k2) ∧
      HasDerivAt (fun x => duoGross2 β (Tstar1 β k1 k2) x - k2 * x ^ 2) 0 (Tstar2 β k1 k2)) := CrossLicensing.Innovation.proposition_2 β k1 k2 h
