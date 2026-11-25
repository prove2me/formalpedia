-- Prove2me | solution 1 for DeficitBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:54:27.9988+00:00
-- url     : https://prove2.me/submissions/56b8b7d8-6694-4a4b-9cc4-c4a9810e6a43

module
public import Definitions.Def_PHarmonicPoly_DeficitPoly
public import Definitions.Def_PHarmonicPoly_TrigPolyEvenPart
public import Definitions.Def_PHarmonicPoly_PolyCosSecondDeriv
public import Definitions.Def_PHarmonicPoly_TrigPolySmooth
public import Definitions.Def_PHarmonicPoly_DeficitBound
public import Theorems.Thm_DeficitPoly
public import Theorems.Thm_PolyCosSecondDeriv
public import Theorems.Thm_TrigPolyEvenPart
public import Theorems.Thm_TrigPolySmooth


set_option autoImplicit false
@[expose] public section
public section
theorem _root_.solution {m : ℕ} (hm : 2 ≤ m) {T : ℝ → ℝ} (hT : TrigPolyLe m T)
    (hbd : ∀ t : ℝ, |T t| ≤ 1) (h0 : T 0 = 1) :
    (0 ≤ 1 + T (Real.pi / m) ∧ 0 ≤ 1 + T (-(Real.pi / m)))
      ∧ (1 + T (Real.pi / m)
            ≤ ((m : ℝ) ^ 2 + iteratedDeriv 2 T 0) * (1 - Real.cos (Real.pi / m))
          ∧ 1 + T (-(Real.pi / m))
            ≤ ((m : ℝ) ^ 2 + iteratedDeriv 2 T 0) * (1 - Real.cos (Real.pi / m)))
      ∧ ((m : ℝ) ^ 2 + iteratedDeriv 2 T 0) * (1 - Real.cos (Real.pi / m))
          ≤ Real.pi ^ 2 * ((m : ℝ) ^ 2 + iteratedDeriv 2 T 0) / (2 * (m : ℝ) ^ 2) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by
    have : 0 < m := by omega
    exact_mod_cast this
  -- Step 0: smoothness
  have hTC : ContDiff ℝ 2 T := (TrigPolySmooth hT).of_le le_top
  -- Step 1
  have hge : ∀ t : ℝ, 0 ≤ 1 + T t := by
    intro t
    have := hbd t
    rw [abs_le] at this
    linarith [this.1]
  -- Step 2
  obtain ⟨P, hPdeg, hPeq⟩ := TrigPolyEvenPart hT
  -- Step 2a
  have hPbd : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |P.eval x| ≤ 1 := by
    intro x hx
    rw [Set.mem_Icc] at hx
    have hc : Real.cos (Real.arccos x) = x := Real.cos_arccos hx.1 hx.2
    rw [← hc, hPeq (Real.arccos x)]
    rw [abs_div]
    rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    have h1 := hbd (Real.arccos x)
    have h2 := hbd (-Real.arccos x)
    rw [abs_le] at h1 h2
    rw [div_le_one (by norm_num), abs_le]
    constructor <;> linarith
  -- Step 2b
  have hP1 : P.eval 1 = 1 := by
    have h := hPeq 0
    rw [Real.cos_zero, neg_zero, h0] at h
    rw [h]; norm_num
  -- Step 2c
  have hPd : (Polynomial.derivative P).eval 1 = -(iteratedDeriv 2 T 0) := by
    have hfun : (fun t : ℝ => P.eval (Real.cos t)) = fun t : ℝ => (T t + T (-t)) / 2 := by
      funext t; exact hPeq t
    have hG := PolyCosSecondDeriv P
    rw [hfun] at hG
    have hE : iteratedDeriv 2 (fun t : ℝ => (T t + T (-t)) / 2) 0 = iteratedDeriv 2 T 0 := by
      have hdiv : iteratedDeriv 2 (fun t : ℝ => (T t + T (-t)) / 2) 0
          = iteratedDeriv 2 (fun t : ℝ => T t + T (-t)) 0 / 2 :=
        iteratedDeriv_div_const (fun t : ℝ => T t + T (-t)) 2
      have hneg : ContDiffAt ℝ 2 (fun t : ℝ => T (-t)) 0 :=
        hTC.contDiffAt.comp 0 (contDiff_neg.contDiffAt)
      have hadd : iteratedDeriv 2 (fun t : ℝ => T t + T (-t)) 0
          = iteratedDeriv 2 T 0 + iteratedDeriv 2 (fun t : ℝ => T (-t)) 0 :=
        iteratedDeriv_fun_add hTC.contDiffAt hneg
      have hcn : iteratedDeriv 2 (fun t : ℝ => T (-t)) 0
          = ((-1 : ℝ)) ^ 2 • iteratedDeriv 2 T (-0) := iteratedDeriv_comp_neg 2 T 0
      rw [hdiv, hadd, hcn]
      norm_num
    rw [hE] at hG
    linarith [hG]
  -- node m 1 = cos (π/m)
  have hnode : Polynomial.Chebyshev.node m 1 = Real.cos (Real.pi / m) := by
    rw [Polynomial.Chebyshev.node]
    norm_num
  -- Step 3
  have halg := DeficitPoly hm hPdeg hPbd hP1
  rw [hnode, hPd] at halg
  -- Step 4
  have hsplit : 2 * (1 + P.eval (Real.cos (Real.pi / m)))
      = (1 + T (Real.pi / m)) + (1 + T (-(Real.pi / m))) := by
    rw [hPeq (Real.pi / m)]; ring
  rw [hsplit] at halg
  have hd := hge (Real.pi / m)
  have hd' := hge (-(Real.pi / m))
  have hmid1 : 1 + T (Real.pi / m)
      ≤ ((m : ℝ) ^ 2 + iteratedDeriv 2 T 0) * (1 - Real.cos (Real.pi / m)) := by
    nlinarith [halg, hd, hd']
  have hmid2 : 1 + T (-(Real.pi / m))
      ≤ ((m : ℝ) ^ 2 + iteratedDeriv 2 T 0) * (1 - Real.cos (Real.pi / m)) := by
    nlinarith [halg, hd, hd']
  -- Step 5: d ≥ 0
  have hhpos : 0 < Real.pi / (m : ℝ) := by positivity
  have hhle : Real.pi / (m : ℝ) ≤ Real.pi := by
    have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.one_le_of_lt hm
    exact div_le_self Real.pi_pos.le h1
  have hcoslt : Real.cos (Real.pi / (m : ℝ)) < 1 := by
    have h := Real.strictAntiOn_cos (Set.mem_Icc.mpr ⟨le_refl 0, Real.pi_pos.le⟩)
      (Set.mem_Icc.mpr ⟨hhpos.le, hhle⟩) hhpos
    rwa [Real.cos_zero] at h
  have hpos : 0 < 1 - Real.cos (Real.pi / (m : ℝ)) := by linarith
  have hdnn : 0 ≤ (m : ℝ) ^ 2 + iteratedDeriv 2 T 0 := by
    by_contra hneg
    rw [not_le] at hneg
    nlinarith [hmid1, hd, hpos]
  -- Step 6
  have hcb : 1 - (Real.pi / (m:ℝ)) ^ 2 / 2 ≤ Real.cos (Real.pi / (m:ℝ)) :=
    Real.one_sub_sq_div_two_le_cos
  have hlast : ((m : ℝ) ^ 2 + iteratedDeriv 2 T 0) * (1 - Real.cos (Real.pi / m))
      ≤ Real.pi ^ 2 * ((m : ℝ) ^ 2 + iteratedDeriv 2 T 0) / (2 * (m : ℝ) ^ 2) := by
    have hbound : 1 - Real.cos (Real.pi / (m:ℝ)) ≤ Real.pi ^ 2 / (2 * (m:ℝ) ^ 2) := by
      have hsq : (Real.pi / (m:ℝ)) ^ 2 / 2 = Real.pi ^ 2 / (2 * (m:ℝ) ^ 2) := by
        field_simp
      rw [← hsq]; linarith
    calc ((m : ℝ) ^ 2 + iteratedDeriv 2 T 0) * (1 - Real.cos (Real.pi / m))
        ≤ ((m : ℝ) ^ 2 + iteratedDeriv 2 T 0) * (Real.pi ^ 2 / (2 * (m:ℝ) ^ 2)) := by
          exact mul_le_mul_of_nonneg_left hbound hdnn
      _ = Real.pi ^ 2 * ((m : ℝ) ^ 2 + iteratedDeriv 2 T 0) / (2 * (m : ℝ) ^ 2) := by ring
  exact ⟨⟨hd, hd'⟩, ⟨hmid1, hmid2⟩, hlast⟩
