-- Prove2me | solution 1 for BNCovPack.Routing.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T21:45:40.030481+00:00
-- url     : https://prove2.me/submissions/ed0f9ba8-919a-4a5a-a6d0-f6be5b2ed56a

import Mathlib
import Definitions.Def_BNCovPack_Routing_Routing
import Definitions.Def_BNCovPack_Routing_FracScheme



namespace BNCovPack.Routing

set_option linter.unusedSectionVars false

section Frac
variable {E : Type*} [Fintype E] [DecidableEq E]

lemma exp_diff_le (c t y : ℝ) (hc : 0 ≤ c) (hy : 0 ≤ y) :
    Real.exp (c * (t + y)) - Real.exp (c * t) ≤ c * y * Real.exp (c * (t + y)) := by
  have h1 : Real.exp (c * t) = Real.exp (c * (t + y)) * Real.exp (-(c * y)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 := Real.add_one_le_exp (-(c * y))
  have h3 := Real.exp_pos (c * (t + y))
  rw [h1]
  nlinarith

lemma xCurve_nonneg (u : E → ℝ) (hu : ∀ e, 0 < u e) (ℓ : ℕ) (B : ℝ) (hB : 0 ≤ B) (e : E) (t : ℝ)
    (ht : 0 ≤ t) : 0 ≤ xCurve u ℓ B e t := by
  unfold xCurve
  have : 1 ≤ Real.exp (B / (2 * u e) * t) := by
    apply Real.one_le_exp
    have := hu e
    positivity
  have : (0 : ℝ) ≤ 1 / (ℓ : ℝ) := by positivity
  nlinarith

lemma xCurve_mono (u : E → ℝ) (hu : ∀ e, 0 < u e) (ℓ : ℕ) (B : ℝ) (hB : 0 ≤ B) (e : E) {t1 t2 : ℝ}
    (h : t1 ≤ t2) : xCurve u ℓ B e t1 ≤ xCurve u ℓ B e t2 := by
  unfold xCurve
  have := hu e
  gcongr

lemma zCurve_nonneg (ℓ : ℕ) (B : ℝ) (hB : 0 ≤ B) (t : ℝ) (ht : 0 ≤ t) : 0 ≤ zCurve ℓ B t := by
  unfold zCurve
  have : 1 ≤ Real.exp (B / 2 * t) := Real.one_le_exp (by positivity)
  have : (0 : ℝ) ≤ 1 / (ℓ : ℝ) := by positivity
  nlinarith

lemma zCurve_mono (ℓ : ℕ) (B : ℝ) (hB : 0 ≤ B) {t1 t2 : ℝ} (h : t1 ≤ t2) :
    zCurve ℓ B t1 ≤ zCurve ℓ B t2 := by
  unfold zCurve
  gcongr

lemma xCurve_le_one (u : E → ℝ) (hu : ∀ e, 0 < u e) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (B : ℝ)
    (hBl : B = 2 * Real.log ((ℓ : ℝ) + 1)) (e : E) (t : ℝ) (h : xCurve u ℓ B e t ≤ 1) : t ≤ u e := by
  unfold xCurve at h
  have hℓ' : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hlog : 0 < Real.log ((ℓ : ℝ) + 1) := Real.log_pos (by linarith)
  have hB : 0 < B := by rw [hBl]; linarith
  have h1 : Real.exp (B / (2 * u e) * t) ≤ (ℓ : ℝ) + 1 := by
    have h0 : (0 : ℝ) < ℓ := by linarith
    have : 1 / (ℓ : ℝ) * (Real.exp (B / (2 * u e) * t) - 1) ≤ 1 := h
    rw [one_div, inv_mul_le_iff₀ h0] at this
    linarith
  have h2 : B / (2 * u e) * t ≤ Real.log ((ℓ : ℝ) + 1) := by
    rw [Real.le_log_iff_exp_le (by linarith)]; exact h1
  have hue := hu e
  have h3 : B / (2 * u e) = Real.log ((ℓ : ℝ) + 1) / u e := by rw [hBl]; field_simp
  rw [h3, div_mul_eq_mul_div, div_le_iff₀ hue] at h2
  nlinarith

lemma zCurve_le_one (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (B : ℝ)
    (hBl : B = 2 * Real.log ((ℓ : ℝ) + 1)) (t : ℝ) (h : zCurve ℓ B t ≤ 1) : t ≤ 1 := by
  unfold zCurve at h
  have hℓ' : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hlog : 0 < Real.log ((ℓ : ℝ) + 1) := Real.log_pos (by linarith)
  have h1 : Real.exp (B / 2 * t) ≤ (ℓ : ℝ) + 1 := by
    have h0 : (0 : ℝ) < ℓ := by linarith
    have : 1 / (ℓ : ℝ) * (Real.exp (B / 2 * t) - 1) ≤ 1 := h
    rw [one_div, inv_mul_le_iff₀ h0] at this
    linarith
  have h2 : B / 2 * t ≤ Real.log ((ℓ : ℝ) + 1) := by
    rw [Real.le_log_iff_exp_le (by linarith)]; exact h1
  have h3 : B / 2 = Real.log ((ℓ : ℝ) + 1) := by rw [hBl]; ring
  rw [h3] at h2
  nlinarith

structure SInv (u : E → ℝ) (ℓ : ℕ) (B : ℝ) (rs : RoundState E) : Prop where
  hx : ∀ e, rs.x e = xCurve u ℓ B e (rs.load e)
  hZ : rs.Z = zCurve ℓ B rs.fr
  hl : ∀ e, 0 ≤ rs.load e
  hfr : 0 ≤ rs.fr
  hx1 : ∀ e, rs.x e ≤ 1
  hZ1 : rs.Z ≤ 1

lemma pathIncrement_spec (u : E → ℝ) (hu : ∀ e, 0 < u e) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (B : ℝ)
    (hBl : B = 2 * Real.log ((ℓ : ℝ) + 1)) (rs : RoundState E) (h : SInv u ℓ B rs) (P : Finset E)
    (hc : ∑ e ∈ P, rs.x e + rs.Z < 1) :
    0 < pathIncrement u ℓ B rs P ∧
      ∑ e ∈ P, xCurve u ℓ B e (rs.load e + pathIncrement u ℓ B rs P) +
        zCurve ℓ B (rs.fr + pathIncrement u ℓ B rs P) = 1 := by
  have hℓ' : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hlog : 0 < Real.log ((ℓ : ℝ) + 1) := Real.log_pos (by linarith)
  have hB : 0 < B := by rw [hBl]; linarith
  set G : ℝ → ℝ := fun y => ∑ e ∈ P, xCurve u ℓ B e (rs.load e + y) + zCurve ℓ B (rs.fr + y) with hGdef
  have hF : ∀ y, 0 ≤ y → pathLHS u ℓ B rs P y = G y := by
    intro y hy
    unfold pathLHS
    rw [hGdef]
    congr 1
    · apply Finset.sum_congr rfl
      intro e _
      apply max_eq_right
      rw [h.hx e]
      exact xCurve_mono u hu ℓ B hB.le e (by linarith)
    · apply max_eq_right
      rw [h.hZ]
      exact zCurve_mono ℓ B hB.le (by linarith)
  have hGcont : Continuous G := by
    rw [hGdef]
    unfold xCurve zCurve
    fun_prop
  have hGmono : ∀ y1 y2, y1 ≤ y2 → G y1 ≤ G y2 := by
    intro y1 y2 hy
    rw [hGdef]
    apply add_le_add
    · apply Finset.sum_le_sum
      intro e _
      exact xCurve_mono u hu ℓ B hB.le e (by linarith)
    · exact zCurve_mono ℓ B hB.le (by linarith)
  have hG0 : G 0 < 1 := by
    rw [hGdef]
    simp only [add_zero]
    have : ∑ e ∈ P, xCurve u ℓ B e (rs.load e) = ∑ e ∈ P, rs.x e :=
      Finset.sum_congr rfl (fun e _ => (h.hx e).symm)
    rw [this, ← h.hZ]; exact hc
  set Y : ℝ := 2 * ℓ / B with hY
  have hY0 : 0 ≤ Y := by positivity
  have hGY : 1 ≤ G Y := by
    rw [hGdef]
    have h1 : 0 ≤ ∑ e ∈ P, xCurve u ℓ B e (rs.load e + Y) :=
      Finset.sum_nonneg (fun e _ => xCurve_nonneg u hu ℓ B hB.le e _ (by linarith [h.hl e]))
    have h2 : 1 ≤ zCurve ℓ B (rs.fr + Y) := by
      unfold zCurve
      have h3 := Real.add_one_le_exp (B / 2 * (rs.fr + Y))
      have h0 : (0 : ℝ) < ℓ := by linarith
      rw [one_div, ← div_eq_inv_mul, le_div_iff₀ h0]
      have : B / 2 * Y = ℓ := by rw [hY]; field_simp
      nlinarith [h.hfr, hB]
    linarith
  obtain ⟨y0, hy0mem, hy0⟩ := intermediate_value_Icc hY0 hGcont.continuousOn ⟨hG0.le, hGY⟩
  have hbdd : BddBelow {y : ℝ | 0 ≤ y ∧ 1 ≤ pathLHS u ℓ B rs P y} := ⟨0, fun y hy => hy.1⟩
  have hSeq : {y : ℝ | 0 ≤ y ∧ 1 ≤ pathLHS u ℓ B rs P y} = {y | 0 ≤ y ∧ 1 ≤ G y} := by
    ext y
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [hF y h1] at h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [hF y h1]⟩
  have hcl : IsClosed {y : ℝ | 0 ≤ y ∧ 1 ≤ pathLHS u ℓ B rs P y} := by
    rw [hSeq]
    exact IsClosed.inter isClosed_Ici (isClosed_le continuous_const hGcont)
  have hne : {y : ℝ | 0 ≤ y ∧ 1 ≤ pathLHS u ℓ B rs P y}.Nonempty :=
    ⟨y0, hy0mem.1, by rw [hF y0 hy0mem.1, hy0]⟩
  have hmem := hcl.csInf_mem hne hbdd
  have hle : sInf {y : ℝ | 0 ≤ y ∧ 1 ≤ pathLHS u ℓ B rs P y} ≤ y0 :=
    csInf_le hbdd ⟨hy0mem.1, by rw [hF y0 hy0mem.1, hy0]⟩
  unfold pathIncrement
  set y := sInf {y : ℝ | 0 ≤ y ∧ 1 ≤ pathLHS u ℓ B rs P y} with hydef
  obtain ⟨hy1, hy2⟩ := hmem
  rw [hF y hy1] at hy2
  have hGy : G y = 1 := le_antisymm (by rw [← hy0]; exact hGmono _ _ hle) hy2
  refine ⟨?_, hGy⟩
  rcases hy1.eq_or_lt with h0 | h0
  · exfalso
    rw [← h0] at hGy
    linarith
  · exact h0


structure StepRes (u : E → ℝ) (ℓ : ℕ) (B : ℝ) (rs rs' : RoundState E) (P : Finset E) (y : ℝ) : Prop where
  hy : 0 ≤ y
  hfs : rs'.fs = rs.fs ++ [y]
  hfr : rs'.fr = rs.fr + y
  hload : ∀ e, rs'.load e = rs.load e + if e ∈ P then y else 0
  hS : SInv u ℓ B rs'
  hcons : 1 ≤ ∑ e ∈ P, rs'.x e + rs'.Z
  hmx : ∀ e, rs.x e ≤ rs'.x e
  hmz : rs.Z ≤ rs'.Z
  hcost : ∑ e, u e * rs'.x e + rs'.Z ≤ ∑ e, u e * rs.x e + rs.Z + B * y

lemma pathStep_res (u : E → ℝ) (hu : ∀ e, 0 < u e) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (B : ℝ)
    (hBl : B = 2 * Real.log ((ℓ : ℝ) + 1)) (rs : RoundState E) (h : SInv u ℓ B rs) (P : Finset E)
    (hP : P.card + 1 ≤ ℓ) : ∃ y, StepRes u ℓ B rs (pathStep u ℓ B rs P) P y := by
  have hℓ' : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hlog : 0 < Real.log ((ℓ : ℝ) + 1) := Real.log_pos (by linarith)
  have hB : 0 < B := by rw [hBl]; linarith
  by_cases hc : 1 ≤ ∑ e ∈ P, rs.x e + rs.Z
  · refine ⟨0, ?_⟩
    have : pathStep u ℓ B rs P = { rs with fs := rs.fs ++ [0] } := by
      unfold pathStep; rw [if_pos hc]
    rw [this]
    exact ⟨le_rfl, rfl, by simp, by simp, ⟨h.hx, h.hZ, h.hl, h.hfr, h.hx1, h.hZ1⟩, hc,
      fun e => le_rfl, le_rfl, by simp⟩
  · have hc' : ∑ e ∈ P, rs.x e + rs.Z < 1 := not_le.mp hc
    obtain ⟨hy0, hLHS⟩ := pathIncrement_spec u hu ℓ hℓ B hBl rs h P hc'
    set y := pathIncrement u ℓ B rs P with hy
    refine ⟨y, ?_⟩
    have hstep : pathStep u ℓ B rs P =
        { x := fun e => if e ∈ P then max (rs.x e) (xCurve u ℓ B e (rs.load e + y)) else rs.x e
          load := fun e => if e ∈ P then rs.load e + y else rs.load e
          Z := max rs.Z (zCurve ℓ B (rs.fr + y))
          fr := rs.fr + y
          fs := rs.fs ++ [y] } := by
      unfold pathStep; rw [if_neg hc]
    have hxe : ∀ e, max (rs.x e) (xCurve u ℓ B e (rs.load e + y)) = xCurve u ℓ B e (rs.load e + y) := by
      intro e
      apply max_eq_right
      rw [h.hx e]
      exact xCurve_mono u hu ℓ B hB.le e (by linarith)
    have hZe : max rs.Z (zCurve ℓ B (rs.fr + y)) = zCurve ℓ B (rs.fr + y) := by
      apply max_eq_right
      rw [h.hZ]
      exact zCurve_mono ℓ B hB.le (by linarith)
    have hxnn : ∀ e, 0 ≤ xCurve u ℓ B e (rs.load e + y) := fun e =>
      xCurve_nonneg u hu ℓ B hB.le e _ (by linarith [h.hl e])
    have hZnn : 0 ≤ zCurve ℓ B (rs.fr + y) := zCurve_nonneg ℓ B hB.le _ (by linarith [h.hfr])
    have hsumnn : 0 ≤ ∑ e ∈ P, xCurve u ℓ B e (rs.load e + y) :=
      Finset.sum_nonneg (fun e _ => hxnn e)
    have hxle : ∀ e ∈ P, xCurve u ℓ B e (rs.load e + y) ≤ 1 := by
      intro e he
      have := Finset.single_le_sum (f := fun e => xCurve u ℓ B e (rs.load e + y))
        (fun e _ => hxnn e) he
      linarith
    have hZle : zCurve ℓ B (rs.fr + y) ≤ 1 := by linarith
    rw [hstep]
    refine ⟨hy0.le, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro e; dsimp only; split_ifs <;> simp
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro e; dsimp only
        split_ifs with he
        · rw [hxe e]
        · exact h.hx e
      · dsimp only; rw [hZe]
      · intro e; dsimp only; split_ifs
        · linarith [h.hl e]
        · exact h.hl e
      · dsimp only; linarith [h.hfr]
      · intro e; dsimp only; split_ifs with he
        · rw [hxe e]; exact hxle e he
        · exact h.hx1 e
      · dsimp only; rw [hZe]; exact hZle
    · dsimp only
      have : ∑ e ∈ P, (if e ∈ P then max (rs.x e) (xCurve u ℓ B e (rs.load e + y)) else rs.x e) =
          ∑ e ∈ P, xCurve u ℓ B e (rs.load e + y) :=
        Finset.sum_congr rfl (fun e he => by rw [if_pos he, hxe e])
      rw [this, hZe, hLHS]
    · intro e; dsimp only; split_ifs
      · exact hxe e ▸ le_max_left _ _
      · exact le_rfl
    · dsimp only; exact le_max_left _ _
    · dsimp only
      have hper : ∀ e, u e * (if e ∈ P then max (rs.x e) (xCurve u ℓ B e (rs.load e + y)) else rs.x e) ≤
          u e * rs.x e + (if e ∈ P then (B / 2) * y * (xCurve u ℓ B e (rs.load e + y) + 1 / (ℓ : ℝ)) else 0) := by
        intro e
        split_ifs with he
        · rw [hxe e]
          have hue := hu e
          have key := exp_diff_le (B / (2 * u e)) (rs.load e) y (by positivity) hy0.le
          have hxx := h.hx e
          unfold xCurve at hxx ⊢
          rw [hxx]
          have hℓ0 : (0 : ℝ) < ℓ := by linarith
          have e1 : u e * (B / (2 * u e)) = B / 2 := by field_simp
          have : u e * (1 / (ℓ : ℝ) * (Real.exp (B / (2 * u e) * (rs.load e + y)) - 1)) -
              u e * (1 / (ℓ : ℝ) * (Real.exp (B / (2 * u e) * rs.load e) - 1)) =
              u e * (1 / (ℓ : ℝ)) * (Real.exp (B / (2 * u e) * (rs.load e + y)) - Real.exp (B / (2 * u e) * rs.load e)) := by ring
          have h2 : u e * (1 / (ℓ : ℝ)) * (Real.exp (B / (2 * u e) * (rs.load e + y)) - Real.exp (B / (2 * u e) * rs.load e)) ≤
              u e * (1 / (ℓ : ℝ)) * (B / (2 * u e) * y * Real.exp (B / (2 * u e) * (rs.load e + y))) :=
            mul_le_mul_of_nonneg_left key (by positivity)
          have h3 : u e * (1 / (ℓ : ℝ)) * (B / (2 * u e) * y * Real.exp (B / (2 * u e) * (rs.load e + y))) =
              B / 2 * y * (1 / (ℓ : ℝ) * (Real.exp (B / (2 * u e) * (rs.load e + y)) - 1) + 1 / (ℓ : ℝ)) := by
            field_simp
            ring
          linarith
        · simp
      have hsum1 := Finset.sum_le_sum (fun e (_ : e ∈ Finset.univ) => hper e)
      rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, ← Finset.mul_sum,
        Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsum1
      rw [hZe]
      have hZ2 : zCurve ℓ B (rs.fr + y) ≤ rs.Z + B / 2 * y * (zCurve ℓ B (rs.fr + y) + 1 / (ℓ : ℝ)) := by
        have key := exp_diff_le (B / 2) (rs.fr) y (by positivity) hy0.le
        have hzz := h.hZ
        unfold zCurve at hzz ⊢
        rw [hzz]
        have hℓ0 : (0 : ℝ) < ℓ := by linarith
        have h2 : 1 / (ℓ : ℝ) * (Real.exp (B / 2 * (rs.fr + y)) - Real.exp (B / 2 * rs.fr)) ≤
            1 / (ℓ : ℝ) * (B / 2 * y * Real.exp (B / 2 * (rs.fr + y))) :=
          mul_le_mul_of_nonneg_left key (by positivity)
        have h3 : 1 / (ℓ : ℝ) * (B / 2 * y * Real.exp (B / 2 * (rs.fr + y))) =
            B / 2 * y * (1 / (ℓ : ℝ) * (Real.exp (B / 2 * (rs.fr + y)) - 1) + 1 / (ℓ : ℝ)) := by
          field_simp
          ring
        nlinarith
      have hcardle : ((P.card : ℝ) + 1) * (1 / (ℓ : ℝ)) ≤ 1 := by
        have hℓ0 : (0 : ℝ) < ℓ := by linarith
        have : (P.card : ℝ) + 1 ≤ ℓ := by exact_mod_cast hP
        rw [← div_eq_mul_one_div, div_le_one hℓ0]; exact this
      have hBy : 0 ≤ B / 2 * y := by positivity
      have hfin : B / 2 * y * (∑ e ∈ P, xCurve u ℓ B e (rs.load e + y) + zCurve ℓ B (rs.fr + y) +
          ((P.card : ℝ) + 1) * (1 / (ℓ : ℝ))) ≤ B / 2 * y * (1 + 1) :=
        mul_le_mul_of_nonneg_left (by rw [hLHS]; linarith) hBy
      nlinarith


structure FoldRes (u : E → ℝ) (ℓ : ℕ) (B : ℝ) (rs rs' : RoundState E) (ps : List (Finset E))
    (fsn : List ℝ) : Prop where
  hlen : fsn.length = ps.length
  hnn : ∀ y ∈ fsn, 0 ≤ y
  hfs : rs'.fs = rs.fs ++ fsn
  hfr : rs'.fr = rs.fr + fsn.sum
  hload : ∀ e, rs'.load e = rs.load e + pathLoad e ps fsn
  hS : SInv u ℓ B rs'
  hcons : ∀ P ∈ ps, 1 ≤ ∑ e ∈ P, rs'.x e + rs'.Z
  hmx : ∀ e, rs.x e ≤ rs'.x e
  hmz : rs.Z ≤ rs'.Z
  hcost : ∑ e, u e * rs'.x e + rs'.Z ≤ ∑ e, u e * rs.x e + rs.Z + B * fsn.sum

lemma fold_res (u : E → ℝ) (hu : ∀ e, 0 < u e) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (B : ℝ)
    (hBl : B = 2 * Real.log ((ℓ : ℝ) + 1)) :
    ∀ (ps : List (Finset E)) (rs : RoundState E), (∀ P ∈ ps, P.card + 1 ≤ ℓ) → SInv u ℓ B rs →
      ∃ fsn, FoldRes u ℓ B rs (ps.foldl (pathStep u ℓ B) rs) ps fsn := by
  intro ps
  induction ps with
  | nil =>
    intro rs _ h
    refine ⟨[], ?_⟩
    simp only [List.foldl_nil]
    exact ⟨rfl, by simp, by simp, by simp, by simp [pathLoad], h, by simp, fun e => le_rfl, le_rfl, by simp⟩
  | cons P ps ih =>
    intro rs hP h
    obtain ⟨y, hy⟩ := pathStep_res u hu ℓ hℓ B hBl rs h P (hP P (List.mem_cons_self))
    obtain ⟨fsn, hf⟩ := ih (pathStep u ℓ B rs P) (fun Q hQ => hP Q (List.mem_cons_of_mem _ hQ)) hy.hS
    refine ⟨y :: fsn, ?_⟩
    rw [List.foldl_cons]
    refine ⟨by simp [hf.hlen], ?_, ?_, ?_, ?_, hf.hS, ?_, ?_, ?_, ?_⟩
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hy.hy
      · exact hf.hnn z hz
    · rw [hf.hfs, hy.hfs]; simp
    · rw [hf.hfr, hy.hfr]; simp; ring
    · intro e
      rw [hf.hload, hy.hload]; simp only [pathLoad]; ring
    · intro Q hQ
      rcases List.mem_cons.mp hQ with rfl | hQ
      · have h1 := hy.hcons
        have h2 : ∑ e ∈ Q, (pathStep u ℓ B rs Q).x e ≤ ∑ e ∈ Q, (ps.foldl (pathStep u ℓ B) (pathStep u ℓ B rs Q)).x e :=
          Finset.sum_le_sum (fun e _ => hf.hmx e)
        have h3 := hf.hmz
        linarith
      · exact hf.hcons Q hQ
    · intro e; exact le_trans (hy.hmx e) (hf.hmx e)
    · exact le_trans hy.hmz hf.hmz
    · have := hy.hcost
      have := hf.hcost
      simp only [List.sum_cons]
      nlinarith

structure FInv (u : E → ℝ) (ℓ : ℕ) (B : ℝ) (σ : List (List (Finset E))) (st : FracState E) : Prop where
  shape : List.Forall₂ (fun ps (fs : List ℝ) => fs.length = ps.length ∧ (∀ y ∈ fs, 0 ≤ y) ∧ fs.sum ≤ 1) σ st.flows
  load_eq : ∀ e, st.load e = edgeLoad e σ st.flows
  hx : ∀ e, st.x e = xCurve u ℓ B e (st.load e)
  load_nn : ∀ e, 0 ≤ st.load e
  x_le : ∀ e, st.x e ≤ 1
  cons : List.Forall₂ (fun ps (fs : List ℝ) =>
    0 ≤ zCurve ℓ B fs.sum ∧ ∀ P ∈ ps, 1 ≤ ∑ e ∈ P, st.x e + zCurve ℓ B fs.sum) σ st.flows
  cost : ∑ e, u e * st.x e + (st.flows.map fun fs => zCurve ℓ B fs.sum).sum ≤ B * routingValue st.flows

lemma forall₂_snoc {α β : Type*} {R : α → β → Prop} {l1 : List α} {l2 : List β}
    (h : List.Forall₂ R l1 l2) {a : α} {b : β} (hab : R a b) :
    List.Forall₂ R (l1 ++ [a]) (l2 ++ [b]) := by
  induction h with
  | nil => exact List.Forall₂.cons hab List.Forall₂.nil
  | cons hr _ ih => exact List.Forall₂.cons hr ih

lemma edgeLoad_snoc (e : E) {R : List (Finset E) → List ℝ → Prop} {σ : List (List (Finset E))}
    {f : List (List ℝ)} (h : List.Forall₂ R σ f) (ps : List (Finset E)) (fs : List ℝ) :
    edgeLoad e (σ ++ [ps]) (f ++ [fs]) = edgeLoad e σ f + pathLoad e ps fs := by
  induction h with
  | nil => simp [edgeLoad]
  | cons hr _ ih => simp only [List.cons_append, edgeLoad, ih]; ring

lemma FInv_init (u : E → ℝ) (ℓ : ℕ) (B : ℝ) : FInv u ℓ B [] (FracState.init E) := by
  refine ⟨List.Forall₂.nil, ?_, ?_, ?_, ?_, List.Forall₂.nil, ?_⟩
  · intro e; simp [FracState.init, edgeLoad]
  · intro e; simp [FracState.init, xCurve]
  · intro e; simp [FracState.init]
  · intro e; simp [FracState.init]
  · simp [FracState.init, routingValue]

lemma fracStep_inv (u : E → ℝ) (hu : ∀ e, 0 < u e) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (B : ℝ)
    (hBl : B = 2 * Real.log ((ℓ : ℝ) + 1)) (σ : List (List (Finset E))) (st : FracState E)
    (ps : List (Finset E)) (hP : ∀ P ∈ ps, P.card + 1 ≤ ℓ) (h : FInv u ℓ B σ st) :
    FInv u ℓ B (σ ++ [ps]) (fracStep u ℓ B st ps) := by
  have hℓ' : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hlog : 0 < Real.log ((ℓ : ℝ) + 1) := Real.log_pos (by linarith)
  have hB : 0 < B := by rw [hBl]; linarith
  have hS0 : SInv u ℓ B ⟨st.x, st.load, 0, 0, []⟩ :=
    ⟨h.hx, by simp [zCurve], h.load_nn, le_rfl, h.x_le, zero_le_one⟩
  obtain ⟨fsn, hr⟩ := fold_res u hu ℓ hℓ B hBl ps ⟨st.x, st.load, 0, 0, []⟩ hP hS0
  have hfs : (ps.foldl (pathStep u ℓ B) ⟨st.x, st.load, 0, 0, []⟩).fs = fsn := by
    simpa using hr.hfs
  have hfr : (ps.foldl (pathStep u ℓ B) ⟨st.x, st.load, 0, 0, []⟩).fr = fsn.sum := by
    simpa using hr.hfr
  have hZ : (ps.foldl (pathStep u ℓ B) ⟨st.x, st.load, 0, 0, []⟩).Z = zCurve ℓ B fsn.sum := by
    rw [hr.hS.hZ, hfr]
  have hsum1 : fsn.sum ≤ 1 := by
    have := hr.hS.hZ1
    rw [hZ] at this
    exact zCurve_le_one ℓ hℓ B hBl _ this
  have hsum0 : 0 ≤ fsn.sum := List.sum_nonneg hr.hnn
  generalize hrs : ps.foldl (pathStep u ℓ B) ⟨st.x, st.load, 0, 0, []⟩ = rs' at hr hfs hfr hZ
  have hfrac : fracStep u ℓ B st ps = ⟨rs'.x, rs'.load, st.flows ++ [fsn]⟩ := by
    unfold fracStep
    simp only [hrs, hfs]
  rw [hfrac]
  have hz0 : 0 ≤ zCurve ℓ B fsn.sum := zCurve_nonneg ℓ B hB.le _ hsum0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact forall₂_snoc h.shape ⟨hr.hlen, hr.hnn, hsum1⟩
  · intro e
    show rs'.load e = _
    rw [hr.hload e, edgeLoad_snoc e h.shape, ← h.load_eq e]
  · intro e; exact hr.hS.hx e
  · intro e; exact hr.hS.hl e
  · intro e; exact hr.hS.hx1 e
  · have := h.cons.imp (fun ps (fs : List ℝ) (hh : 0 ≤ zCurve ℓ B fs.sum ∧ ∀ P ∈ ps, 1 ≤ ∑ e ∈ P, st.x e + zCurve ℓ B fs.sum) =>
      (⟨hh.1, fun P hP => le_trans (hh.2 P hP) (by
        have h1 : ∑ e ∈ P, st.x e ≤ ∑ e ∈ P, rs'.x e := Finset.sum_le_sum (fun e _ => hr.hmx e)
        show _ ≤ ∑ e ∈ P, rs'.x e + zCurve ℓ B fs.sum
        linarith)⟩ : 0 ≤ zCurve ℓ B fs.sum ∧ ∀ P ∈ ps, 1 ≤ ∑ e ∈ P, rs'.x e + zCurve ℓ B fs.sum))
    refine forall₂_snoc this ⟨hz0, fun P hP' => ?_⟩
    have := hr.hcons P hP'
    rw [hZ] at this
    exact this
  · show ∑ e, u e * rs'.x e + ((st.flows ++ [fsn]).map fun (fs : List ℝ) => zCurve ℓ B fs.sum).sum ≤
      B * routingValue (st.flows ++ [fsn])
    have hc := hr.hcost
    rw [hfr, hZ] at *
    simp only [routingValue, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hc ⊢
    have h2 := h.cost
    simp only [routingValue] at h2
    have h3 : ∑ e, u e * (⟨st.x, st.load, 0, 0, []⟩ : RoundState E).x e = ∑ e, u e * st.x e := rfl
    simp only [zCurve, Nat.cast_zero] at *
    linarith


lemma fracRun_inv (u : E → ℝ) (hu : ∀ e, 0 < u e) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (B : ℝ)
    (hBl : B = 2 * Real.log ((ℓ : ℝ) + 1)) (σ : List (List (Finset E)))
    (hP : ∀ ps ∈ σ, ∀ P ∈ ps, P.card + 1 ≤ ℓ) : FInv u ℓ B σ (fracRun u ℓ B σ) := by
  induction σ using List.reverseRecOn with
  | nil => exact FInv_init u ℓ B
  | append_singleton σ ps ih =>
    have h1 := ih (fun qs hq => hP qs (List.mem_append_left _ hq))
    have : fracRun u ℓ B (σ ++ [ps]) = fracStep u ℓ B (fracRun u ℓ B σ) ps := by
      simp [fracRun, List.foldl_append]
    rw [this]
    exact fracStep_inv u hu ℓ hℓ B hBl σ _ ps (hP ps (by simp)) h1

lemma weak_dual_path (x : E → ℝ) (Z : ℝ) :
    ∀ (ps : List (Finset E)) (g : List ℝ), g.length = ps.length → (∀ y ∈ g, 0 ≤ y) →
      (∀ P ∈ ps, 1 ≤ ∑ e ∈ P, x e + Z) →
      g.sum ≤ ∑ e, x e * pathLoad e ps g + Z * g.sum := by
  intro ps
  induction ps with
  | nil => intro g hlen _ _; cases g <;> simp_all [pathLoad]
  | cons P ps ih =>
    intro g hlen hnn hc
    cases g with
    | nil => simp at hlen
    | cons y ys =>
      have hy : 0 ≤ y := hnn y (by simp)
      have ih' := ih ys (by simpa using hlen) (fun z hz => hnn z (by simp [hz]))
        (fun Q hQ => hc Q (by simp [hQ]))
      have h1 := hc P (by simp)
      have h2 : ∑ e, x e * pathLoad e (P :: ps) (y :: ys) =
          y * ∑ e ∈ P, x e + ∑ e, x e * pathLoad e ps ys := by
        simp only [pathLoad, mul_add, Finset.sum_add_distrib]
        congr 1
        simp only [mul_ite, mul_zero]
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      simp only [List.sum_cons]
      rw [h2]
      nlinarith


lemma weak_dual_run (ℓ : ℕ) (B : ℝ) (x : E → ℝ) (hx : ∀ e, 0 ≤ x e) :
    ∀ (σ : List (List (Finset E))) (f flows : List (List ℝ)),
      List.Forall₂ (fun ps (fs : List ℝ) => fs.length = ps.length ∧ ∀ y ∈ fs, 0 ≤ y) σ f →
      (∀ fs ∈ f, fs.sum ≤ 1) →
      List.Forall₂ (fun ps (fs : List ℝ) =>
        0 ≤ zCurve ℓ B fs.sum ∧ ∀ P ∈ ps, 1 ≤ ∑ e ∈ P, x e + zCurve ℓ B fs.sum) σ flows →
      routingValue f ≤ ∑ e, x e * edgeLoad e σ f + (flows.map fun (fs : List ℝ) => zCurve ℓ B fs.sum).sum := by
  intro σ
  induction σ with
  | nil =>
    intro f flows hf _ hc
    cases f with
    | nil => cases flows with
      | nil => simp [routingValue, edgeLoad]
      | cons _ _ => simp at hc
    | cons _ _ => simp at hf
  | cons ps σ ih =>
    intro f flows hf hf1 hc
    cases f with
    | nil => simp at hf
    | cons g f' =>
      cases flows with
      | nil => simp at hc
      | cons h flows' =>
        obtain ⟨⟨hlen, hnn⟩, hf'⟩ := List.forall₂_cons.mp hf
        obtain ⟨⟨hz, hcons⟩, hc'⟩ := List.forall₂_cons.mp hc
        have ih' := ih f' flows' hf' (fun fs hfs => hf1 fs (List.mem_cons_of_mem _ hfs)) hc'
        have hg1 : g.sum ≤ 1 := hf1 g (List.mem_cons_self)
        have hd := weak_dual_path x (zCurve ℓ B h.sum) ps g hlen hnn hcons
        have hzg : zCurve ℓ B h.sum * g.sum ≤ zCurve ℓ B h.sum := by nlinarith
        have : ∑ e, x e * edgeLoad e (ps :: σ) (g :: f') =
            ∑ e, x e * pathLoad e ps g + ∑ e, x e * edgeLoad e σ f' := by
          simp only [edgeLoad, mul_add, Finset.sum_add_distrib]
        rw [this]
        simp only [routingValue, List.map_cons, List.sum_cons] at ih' ⊢
        linarith

lemma forall₂_mem_right {α β : Type*} {R : α → β → Prop} {l1 : List α} {l2 : List β}
    (h : List.Forall₂ R l1 l2) {b : β} (hb : b ∈ l2) : ∃ a ∈ l1, R a b := by
  induction h with
  | nil => simp at hb
  | cons hr _ ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨a, ha, hra⟩ := ih hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hra⟩

theorem thm32_core (u : E → ℝ) (hu : ∀ e, 0 < u e) (Pmax : ℕ) (σ : List (List (Finset E)))
    (hP : ∀ ps ∈ σ, ∀ P ∈ ps, P.card ≤ Pmax) :
    IsFeasibleRouting u σ (fracRun u (Pmax + 1) (2 * Real.log ((Pmax : ℝ) + 2)) σ).flows ∧
    ∀ f : List (List ℝ), IsFeasibleRouting u σ f →
      routingValue f ≤ 2 * Real.log ((Pmax : ℝ) + 2) *
        routingValue (fracRun u (Pmax + 1) (2 * Real.log ((Pmax : ℝ) + 2)) σ).flows := by
  have hBl : 2 * Real.log ((Pmax : ℝ) + 2) = 2 * Real.log (((Pmax + 1 : ℕ) : ℝ) + 1) := by
    congr 2; push_cast; ring
  have hinv := fracRun_inv u hu (Pmax + 1) (by omega) _ hBl σ
    (fun ps hps P hP' => by have := hP ps hps P hP'; omega)
  set B := 2 * Real.log ((Pmax : ℝ) + 2) with hB
  set st := fracRun u (Pmax + 1) B σ with hst
  have hℓ' : (1 : ℝ) ≤ ((Pmax + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ Pmax + 1)
  have hlog : 0 < Real.log ((Pmax : ℝ) + 2) := Real.log_pos (by
    have : (0 : ℝ) ≤ Pmax := Nat.cast_nonneg _
    linarith)
  have hB0 : 0 < B := by rw [hB]; linarith
  have hloadle : ∀ e, st.load e ≤ u e := fun e =>
    xCurve_le_one u hu (Pmax + 1) (by omega) B hBl e _ (by rw [← hinv.hx e]; exact hinv.x_le e)
  constructor
  · refine ⟨hinv.shape.imp (fun ps fs h => ⟨h.1, h.2.1⟩), ?_, ?_⟩
    · intro fs hfs
      obtain ⟨ps, _, h⟩ := forall₂_mem_right hinv.shape hfs
      exact h.2.2
    · intro e
      rw [← hinv.load_eq e]; exact hloadle e
  · intro f hf
    obtain ⟨hf1, hf2, hf3⟩ := hf
    have hxnn : ∀ e, 0 ≤ st.x e := fun e => by
      rw [hinv.hx e]
      exact xCurve_nonneg u hu _ B hB0.le e _ (hinv.load_nn e)
    have hwd := weak_dual_run (Pmax + 1) B st.x hxnn σ f st.flows hf1 hf2 hinv.cons
    have hZnn : 0 ≤ (st.flows.map fun (fs : List ℝ) => zCurve (Pmax + 1) B fs.sum).sum := by
      apply List.sum_nonneg
      intro z hz
      simp only [List.mem_map] at hz
      obtain ⟨fs, hfs, rfl⟩ := hz
      obtain ⟨ps, _, h⟩ := forall₂_mem_right hinv.cons hfs
      exact h.1
    have h1 : ∑ e, st.x e * edgeLoad e σ f ≤ ∑ e, u e * st.x e := by
      apply Finset.sum_le_sum
      intro e _
      have := mul_le_mul_of_nonneg_left (hf3 e) (hxnn e)
      linarith
    have := hinv.cost
    linarith

end Frac
end BNCovPack.Routing

open BNCovPack.Routing


theorem solution {E : Type*} [Fintype E] [DecidableEq E] (u : E → ℝ) (hu : ∀ e, 0 < u e)
    (Pmax : ℕ) (σ : List (List (Finset E))) (hP : ∀ ps ∈ σ, ∀ P ∈ ps, P.card ≤ Pmax) :
    IsFeasibleRouting u σ (fracRun u (Pmax + 1) (2 * Real.log ((Pmax : ℝ) + 2)) σ).flows ∧
    ∀ f : List (List ℝ), IsFeasibleRouting u σ f →
      routingValue f ≤ 2 * Real.log ((Pmax : ℝ) + 2) *
        routingValue (fracRun u (Pmax + 1) (2 * Real.log ((Pmax : ℝ) + 2)) σ).flows := by
  exact thm32_core u hu Pmax σ hP
