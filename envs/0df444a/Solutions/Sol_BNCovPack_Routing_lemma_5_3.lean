-- Prove2me | solution 1 for BNCovPack.Routing.lemma_5_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T21:38:03.944979+00:00
-- url     : https://prove2.me/submissions/4022ad9d-d3ad-420c-9d7f-c1ef3d88979a

import Mathlib
import Definitions.Def_BNCovPack_Routing_Routing
import Definitions.Def_BNCovPack_Routing_Potential
import Definitions.Def_BNCovPack_Routing_Algorithm



namespace BNCovPack.Routing

set_option linter.unusedSectionVars false

section Pot
variable {E : Type*} [Fintype E] [DecidableEq E]

lemma pathLoad_eq_sum (e : E) : ∀ (ps : List (Finset E)) (g : List ℝ), g.length = ps.length →
    pathLoad e ps g = ((ps.zip g).map (fun Py => if e ∈ Py.1 then Py.2 else 0)).sum
  | [], g, h => by cases g <;> simp [pathLoad]
  | P :: ps, [], h => by simp at h
  | P :: ps, y :: ys, h => by
      simp only [pathLoad, List.zip_cons_cons, List.map_cons, List.sum_cons]
      rw [pathLoad_eq_sum e ps ys (by simpa using h)]

lemma sum_snd_zip' (ps : List (Finset E)) (g : List ℝ) (h : g.length = ps.length) :
    ((ps.zip g).map Prod.snd).sum = g.sum := by
  rw [List.map_snd_zip (by omega)]

lemma list_sum_comm {α : Type*} (J : List α) (h : E → α → ℝ) :
    (J.map fun a => ∑ e, h e a).sum = ∑ e, (J.map fun a => h e a).sum := by
  induction J with
  | nil => simp
  | cons a J ih => simp [ih, Finset.sum_add_distrib]

lemma uMin_le [Nonempty E] (u : E → ℝ) (e : E) : uMin u ≤ u e :=
  Finset.inf'_le _ (Finset.mem_univ e)

lemma uMin_pos [Nonempty E] (u : E → ℝ) (hu : ∀ e, 0 < u e) : 0 < uMin u := by
  unfold uMin
  rw [Finset.lt_inf'_iff]
  intro e _; exact hu e

lemma card_pos' [Nonempty E] : (0 : ℝ) < (Fintype.card E : ℝ) := by
  exact_mod_cast Fintype.card_pos

lemma log2m_nonneg [Nonempty E] : 0 ≤ Real.log (2 * (Fintype.card E : ℝ)) := by
  apply Real.log_nonneg
  have : (1 : ℝ) ≤ (Fintype.card E : ℝ) := by exact_mod_cast Fintype.card_pos
  linarith

lemma scale_gt_one [Nonempty E] (u : E → ℝ) (hu : ∀ e, 0 < u e) : 1 < roundingScale u := by
  unfold roundingScale
  have h1 := uMin_pos u hu
  have h2 : 0 ≤ Real.log (2 * (Fintype.card E : ℝ)) / uMin u := div_nonneg log2m_nonneg h1.le
  have h3 : Real.exp 1 ≤ Real.exp (1 + Real.log (2 * (Fintype.card E : ℝ)) / uMin u) :=
    Real.exp_le_exp.mpr (by linarith)
  have := Real.exp_one_gt_d9
  linarith

lemma exp_c_le [Nonempty E] (u : E → ℝ) (hu : ∀ e, 0 < u e) (e : E) :
    Real.exp (1 + Real.log (2 * (Fintype.card E : ℝ)) / u e) ≤ roundingScale u + 1 := by
  unfold roundingScale
  rw [sub_add_cancel]
  apply Real.exp_le_exp.mpr
  have := div_le_div_of_nonneg_left (log2m_nonneg (E := E)) (uMin_pos u hu) (uMin_le u e)
  linarith


lemma J_sum_expand (J : List (Finset E × ℝ)) (X Y : ℝ) (F : E → Finset E → ℝ) :
    (J.map fun Py => Py.2 * (X + Y * ∑ e, F e Py.1)).sum =
      (J.map Prod.snd).sum * X + Y * ∑ e, (J.map fun Py => Py.2 * F e Py.1).sum := by
  induction J with
  | nil => simp
  | cons a J ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih, Finset.sum_add_distrib]
    have : a.2 * (Y * ∑ e, F e a.1) = Y * ∑ e, a.2 * F e a.1 := by
      rw [← Finset.mul_sum]; ring
    rw [mul_add, this]; ring

lemma edge_expand (J : List (Finset E × ℝ)) (e : E) (K ec : ℝ) :
    (J.map fun Py => Py.2 * (K * (if e ∈ Py.1 then ec else 1))).sum =
      K * ((J.map Prod.snd).sum + (J.map fun Py => if e ∈ Py.1 then Py.2 else 0).sum * (ec - 1)) := by
  have : ∀ Py : Finset E × ℝ, Py.2 * (K * (if e ∈ Py.1 then ec else 1)) =
      K * (Py.2 + (if e ∈ Py.1 then Py.2 else 0) * (ec - 1)) := by
    intro Py; split_ifs <;> ring
  simp only [this, List.sum_map_mul_left]
  congr 1
  induction J with
  | nil => simp
  | cons a J ih =>
    simp only [List.map_cons, List.sum_cons, add_mul] at ih ⊢
    rw [ih]; ring

lemma exp_mul_one_sub_le (x : ℝ) : Real.exp x * (1 - x) ≤ 1 := by
  have h := Real.add_one_le_exp (-x)
  have h2 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  have h3 := Real.exp_pos x
  nlinarith

lemma comb_real (J : List (Finset E × ℝ)) (W G a0 m : ℝ) (c d pl : E → ℝ)
    (hW : 1 < W) (hG : G = (J.map Prod.snd).sum) (hG1 : G ≤ 1) (ha0 : 0 < a0) (hm : 0 < m)
    (hd : ∀ e, 0 ≤ d e) (hc : ∀ e, Real.exp (c e) ≤ W + 1)
    (hpl : ∀ e, pl e = (J.map fun Py => if e ∈ Py.1 then Py.2 else 0).sum)
    (hpl0 : ∀ e, 0 ≤ pl e) :
    (W - G) * ((1 / 2) * (a0 * Real.exp (G / (2 * W))) + (1 / (2 * m)) * ∑ e, d e * Real.exp (-pl e)) +
      (J.map fun Py => Py.2 * ((1 / 2) * (a0 * Real.exp (G / (2 * W)) / 2) +
        (1 / (2 * m)) * ∑ e, d e * Real.exp (-pl e) * (if e ∈ Py.1 then Real.exp (c e) else 1))).sum
      ≤ W * ((1 / 2) * a0 + (1 / (2 * m)) * ∑ e, d e) := by
  rw [J_sum_expand J ((1 / 2) * (a0 * Real.exp (G / (2 * W)) / 2)) (1 / (2 * m))
    (fun e P => d e * Real.exp (-pl e) * (if e ∈ P then Real.exp (c e) else 1))]
  have hE : ∀ e, (J.map fun Py => Py.2 * (d e * Real.exp (-pl e) * (if e ∈ Py.1 then Real.exp (c e) else 1))).sum
      = d e * Real.exp (-pl e) * (G + pl e * (Real.exp (c e) - 1)) := by
    intro e
    rw [edge_expand J e (d e * Real.exp (-pl e)) (Real.exp (c e)), ← hG, ← hpl e]
  simp only [hE]
  rw [← hG]
  have hq := exp_mul_one_sub_le (G / (2 * W))
  have hWpos : 0 < W := by linarith
  have hq2 : Real.exp (G / (2 * W)) * (W - G / 2) ≤ W := by
    have : W - G / 2 = W * (1 - G / (2 * W)) := by field_simp
    rw [this]; nlinarith [Real.exp_pos (G / (2 * W))]
  have hEdge : ∀ e, d e * Real.exp (-pl e) * (G + pl e * (Real.exp (c e) - 1)) + (W - G) * (d e * Real.exp (-pl e)) ≤ W * d e := by
    intro e
    have h1 : Real.exp (-pl e) * (1 + pl e) ≤ 1 := by
      have := Real.add_one_le_exp (pl e)
      have h2 : Real.exp (-pl e) * Real.exp (pl e) = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (-pl e)]
    have h3 : pl e * (Real.exp (c e) - 1) ≤ pl e * W := by
      apply mul_le_mul_of_nonneg_left _ (hpl0 e); linarith [hc e]
    have h4 : 0 ≤ d e * Real.exp (-pl e) := mul_nonneg (hd e) (Real.exp_pos _).le
    calc d e * Real.exp (-pl e) * (G + pl e * (Real.exp (c e) - 1)) + (W - G) * (d e * Real.exp (-pl e))
        = d e * Real.exp (-pl e) * (W + pl e * (Real.exp (c e) - 1)) := by ring
      _ ≤ d e * Real.exp (-pl e) * (W + pl e * W) := by
          apply mul_le_mul_of_nonneg_left _ h4; linarith
      _ = W * d e * (Real.exp (-pl e) * (1 + pl e)) := by ring
      _ ≤ W * d e * 1 := by
          apply mul_le_mul_of_nonneg_left h1; exact mul_nonneg hWpos.le (hd e)
      _ = W * d e := by ring
  have hsum : ∑ e, (d e * Real.exp (-pl e) * (G + pl e * (Real.exp (c e) - 1)) + (W - G) * (d e * Real.exp (-pl e)))
      ≤ ∑ e, W * d e := Finset.sum_le_sum (fun e _ => hEdge e)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hm2 : 0 < 1 / (2 * m) := by positivity
  have h5 := mul_le_mul_of_nonneg_left hsum hm2.le
  have h6 : a0 * (Real.exp (G / (2 * W)) * (W - G / 2)) ≤ a0 * W := mul_le_mul_of_nonneg_left hq2 ha0.le
  nlinarith

lemma potential_R [Nonempty E] (u : E → ℝ) (W T G : ℝ) (L pl : E → ℝ) (χ : E → ℕ) (s : ℕ) :
    potential u W (T + G) (fun e => L e + pl e) χ s =
      (1 / 2) * (Real.exp (T / (2 * W) - Real.log 2 * (s : ℝ)) * Real.exp (G / (2 * W))) +
      (1 / (2 * (Fintype.card E : ℝ))) * ∑ e, Real.exp ((1 + Real.log (2 * (Fintype.card E : ℝ)) / u e) * (χ e : ℝ) - L e) * Real.exp (-pl e) := by
  unfold potential
  congr 1
  · rw [← Real.exp_add]; congr 2; ring
  · congr 1
    apply Finset.sum_congr rfl
    intro e _
    rw [← Real.exp_add]; congr 1; ring

lemma potential_S [Nonempty E] (u : E → ℝ) (W T G : ℝ) (L pl : E → ℝ) (χ : E → ℕ) (s : ℕ) (P : Finset E) :
    potential u W (T + G) (fun e => L e + pl e) (addPath χ P) (s + 1) =
      (1 / 2) * (Real.exp (T / (2 * W) - Real.log 2 * (s : ℝ)) * Real.exp (G / (2 * W)) / 2) +
      (1 / (2 * (Fintype.card E : ℝ))) * ∑ e, Real.exp ((1 + Real.log (2 * (Fintype.card E : ℝ)) / u e) * (χ e : ℝ) - L e) * Real.exp (-pl e) *
        (if e ∈ P then Real.exp (1 + Real.log (2 * (Fintype.card E : ℝ)) / u e) else 1) := by
  unfold potential
  congr 1
  · have : Real.exp ((T + G) / (2 * W) - Real.log 2 * ((s + 1 : ℕ) : ℝ)) =
        Real.exp (T / (2 * W) - Real.log 2 * (s : ℝ)) * Real.exp (G / (2 * W)) / 2 := by
      have h2 : Real.exp (-Real.log 2) = 1 / 2 := by
        rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
      rw [show (T + G) / (2 * W) - Real.log 2 * ((s + 1 : ℕ) : ℝ) =
          (T / (2 * W) - Real.log 2 * (s : ℝ)) + G / (2 * W) + (-Real.log 2) by push_cast; ring,
        Real.exp_add, Real.exp_add, h2]; ring
    rw [this]
  · congr 1
    apply Finset.sum_congr rfl
    intro e _
    unfold addPath
    split_ifs
    · rw [← Real.exp_add, ← Real.exp_add]; congr 1; push_cast; ring
    · rw [← Real.exp_add]; rw [mul_one]; congr 1; push_cast; ring

lemma pathLoad_nonneg (e : E) (ps : List (Finset E)) (g : List ℝ) (hlen : g.length = ps.length)
    (hnn : ∀ y ∈ g, 0 ≤ y) : 0 ≤ pathLoad e ps g := by
  rw [pathLoad_eq_sum e ps g hlen]
  apply List.sum_nonneg
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨Py, hPy, rfl⟩ := hx
  split_ifs
  · exact hnn _ (List.of_mem_zip hPy).2
  · exact le_rfl

theorem lemma53_core [Nonempty E] (u : E → ℝ) (hu : ∀ e, 0 < u e) :
    potential u (roundingScale u) 0 (fun _ => 0) (fun _ => 0) 0 ≤ 1 ∧
    (∀ (T : ℝ) (L : E → ℝ) (χ : E → ℕ) (s : ℕ), 0 < potential u (roundingScale u) T L χ s) ∧
    ∀ (T : ℝ) (L : E → ℝ) (χ : E → ℕ) (s : ℕ) (ps : List (Finset E)) (g : List ℝ),
      g.length = ps.length → (∀ y ∈ g, 0 ≤ y) → g.sum ≤ 1 →
      (∃ Py ∈ ps.zip g, 0 < Py.2 ∧
          potential u (roundingScale u) (T + g.sum) (fun e => L e + pathLoad e ps g)
            (addPath χ Py.1) (s + 1) ≤ potential u (roundingScale u) T L χ s) ∨
      potential u (roundingScale u) (T + g.sum) (fun e => L e + pathLoad e ps g) χ s ≤
        potential u (roundingScale u) T L χ s := by
  have hm := card_pos' (E := E)
  refine ⟨?_, ?_, ?_⟩
  · unfold potential
    simp only [zero_div, zero_sub, mul_zero, sub_zero, Real.exp_zero, Nat.cast_zero, zero_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    have : (1 / (2 * (Fintype.card E : ℝ))) * (Fintype.card E : ℝ) = 1 / 2 := by field_simp
    rw [this]; norm_num
  · intro T L χ s
    unfold potential
    have h1 : 0 < (1 / 2 : ℝ) * Real.exp (T / (2 * roundingScale u) - Real.log 2 * (s : ℝ)) := by positivity
    have h2 : 0 ≤ (1 / (2 * (Fintype.card E : ℝ))) * ∑ e, Real.exp ((1 + Real.log (2 * (Fintype.card E : ℝ)) / u e) * (χ e : ℝ) - L e) := by
      apply mul_nonneg (by positivity)
      exact Finset.sum_nonneg (fun e _ => (Real.exp_pos _).le)
    linarith
  · intro T L χ s ps g hlen hnn hsum
    have hW1 := scale_gt_one u hu
    have hJnn : ∀ Py ∈ ps.zip g, 0 ≤ Py.2 := fun Py hPy => hnn _ (List.of_mem_zip hPy).2
    have hGJ : g.sum = ((ps.zip g).map Prod.snd).sum := (sum_snd_zip' ps g hlen).symm
    have hpl : ∀ e, pathLoad e ps g = ((ps.zip g).map fun Py => if e ∈ Py.1 then Py.2 else 0).sum :=
      fun e => pathLoad_eq_sum e ps g hlen
    have hpl0 : ∀ e, 0 ≤ pathLoad e ps g := fun e => pathLoad_nonneg e ps g hlen hnn
    have hG0 : 0 ≤ g.sum := List.sum_nonneg hnn
    by_contra hno
    push_neg at hno
    obtain ⟨hnoS, hnoR⟩ := hno
    have hcomb := comb_real (ps.zip g) (roundingScale u) g.sum (Real.exp (T / (2 * roundingScale u) - Real.log 2 * (s : ℝ)))
      (Fintype.card E : ℝ) (fun e => 1 + Real.log (2 * (Fintype.card E : ℝ)) / u e)
      (fun e => Real.exp ((1 + Real.log (2 * (Fintype.card E : ℝ)) / u e) * (χ e : ℝ) - L e))
      (fun e => pathLoad e ps g) hW1 hGJ hsum (Real.exp_pos _) hm (fun e => (Real.exp_pos _).le)
      (fun e => exp_c_le u hu e) hpl hpl0
    simp only [← potential_R, ← potential_S] at hcomb
    have hΦ : potential u (roundingScale u) T L χ s =
        (1 / 2) * Real.exp (T / (2 * roundingScale u) - Real.log 2 * (s : ℝ)) +
          (1 / (2 * (Fintype.card E : ℝ))) * ∑ e, Real.exp ((1 + Real.log (2 * (Fintype.card E : ℝ)) / u e) * (χ e : ℝ) - L e) := rfl
    rw [← hΦ] at hcomb
    have h1 : ((ps.zip g).map fun Py => Py.2 * potential u (roundingScale u) T L χ s).sum ≤
        ((ps.zip g).map fun Py => Py.2 * potential u (roundingScale u) (T + g.sum)
          (fun e => L e + pathLoad e ps g) (addPath χ Py.1) (s + 1)).sum := by
      apply List.sum_le_sum
      intro Py hPy
      rcases (hJnn Py hPy).eq_or_lt with h0 | hpos
      · rw [← h0]; simp
      · exact mul_le_mul_of_nonneg_left (hnoS Py hPy hpos).le hpos.le
    rw [List.sum_map_mul_right, ← hGJ] at h1
    nlinarith [mul_pos (show 0 < roundingScale u - g.sum by linarith) (sub_pos.mpr hnoR)]

end Pot
end BNCovPack.Routing

open BNCovPack.Routing


theorem solution {E : Type*} [Fintype E] [Nonempty E] [DecidableEq E] (u : E → ℝ)
    (hu : ∀ e, 0 < u e) :
    potential u (roundingScale u) 0 (fun _ => 0) (fun _ => 0) 0 ≤ 1 ∧
    (∀ (T : ℝ) (L : E → ℝ) (χ : E → ℕ) (s : ℕ), 0 < potential u (roundingScale u) T L χ s) ∧
    ∀ (T : ℝ) (L : E → ℝ) (χ : E → ℕ) (s : ℕ) (ps : List (Finset E)) (g : List ℝ),
      g.length = ps.length → (∀ y ∈ g, 0 ≤ y) → g.sum ≤ 1 →
      (∃ Py ∈ ps.zip g, 0 < Py.2 ∧
          potential u (roundingScale u) (T + g.sum) (fun e => L e + pathLoad e ps g)
            (addPath χ Py.1) (s + 1) ≤ potential u (roundingScale u) T L χ s) ∨
      potential u (roundingScale u) (T + g.sum) (fun e => L e + pathLoad e ps g) χ s ≤
        potential u (roundingScale u) T L χ s := by
  exact lemma53_core u hu
