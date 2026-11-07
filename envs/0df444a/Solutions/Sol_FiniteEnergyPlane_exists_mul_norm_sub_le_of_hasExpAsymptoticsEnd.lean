-- Prove2me | solution 1 for FiniteEnergyPlane.exists_mul_norm_sub_le_of_hasExpAsymptoticsEnd
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-06T16:41:07.56578+00:00
-- url     : https://prove2.me/submissions/aaf4cc25-67bb-42bb-98cd-5a5eed4fa431

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Mathlib



namespace FiniteEnergyPlane

open scoped Real

theorem emb_exists_cylInf_eq (z : ℂ) (hz : z ≠ 0) :
    ∃ t : ℝ, cylInf (Real.log ‖z‖ / (2 * π)) t = z := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz
  have h2pi : (0 : ℝ) < 2 * π := by positivity
  have hexp : Real.exp (2 * π * (Real.log ‖z‖ / (2 * π))) = ‖z‖ := by
    rw [mul_div_cancel₀ _ h2pi.ne', Real.exp_log hzpos]
  refine ⟨Complex.arg z / (2 * π), ?_⟩
  unfold cylInf ccwLoop
  rw [hexp]
  have e : ((2 * π * (Complex.arg z / (2 * π)) : ℝ) : ℂ) = (Complex.arg z : ℂ) := by
    congr 1
    field_simp
  rw [e]
  exact Complex.norm_mul_exp_arg_mul_I z

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open Metric Filter Topology
open scoped ContDiff Real

theorem emb_abs_exp_sub_le (x y : ℝ) :
    |Real.exp x - Real.exp y| ≤ (Real.exp x + Real.exp y) * |x - y| := by
  wlog hxy : y ≤ x generalizing x y
  · have := this y x (le_of_not_ge hxy)
    rwa [abs_sub_comm, abs_sub_comm y x, add_comm] at this
  have h1 : Real.exp y ≤ Real.exp x := Real.exp_le_exp.2 hxy
  rw [abs_of_nonneg (sub_nonneg.2 h1), abs_of_nonneg (sub_nonneg.2 hxy)]
  have h2 : 1 - (x - y) ≤ Real.exp (y - x) := by
    have := Real.add_one_le_exp (y - x)
    linarith
  have h3 : Real.exp y = Real.exp x * Real.exp (y - x) := by
    rw [← Real.exp_add]; congr 1; ring
  have hx := Real.exp_pos x
  have hy := Real.exp_pos y
  have h4 : Real.exp x - Real.exp y ≤ Real.exp x * (x - y) := by
    rw [h3]; nlinarith
  have h5 : 0 ≤ Real.exp y * (x - y) := mul_nonneg hy.le (sub_nonneg.2 hxy)
  nlinarith

theorem emb_norm_cylInf (s t : ℝ) : ‖cylInf s t‖ = Real.exp (2 * π * s) := by
  unfold cylInf ccwLoop
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

theorem emb_cylInf_add_int (s t : ℝ) (k : ℤ) : cylInf s (t + k) = cylInf s t := by
  unfold cylInf ccwLoop
  congr 1
  have e : ((2 * π * (t + k) : ℝ) : ℂ) * Complex.I =
      ((2 * π * t : ℝ) : ℂ) * Complex.I + k * (2 * π * Complex.I) := by
    push_cast; ring
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem emb_norm_cylInf_sub_le (s s' t t' : ℝ) :
    ‖cylInf s t - cylInf s' t'‖ ≤
      (Real.exp (2 * π * s) + Real.exp (2 * π * s')) * (2 * π * (|s - s'| + |t - t'|)) := by
  set r := Real.exp (2 * π * s) with hr
  set r' := Real.exp (2 * π * s') with hr'
  have hrpos : 0 < r := Real.exp_pos _
  have hr'pos : 0 < r' := Real.exp_pos _
  set e : ℂ := Complex.exp (((2 * π * t : ℝ) : ℂ) * Complex.I) with he
  set e' : ℂ := Complex.exp (((2 * π * t' : ℝ) : ℂ) * Complex.I) with he'
  have hsplit : cylInf s t - cylInf s' t' = ((r - r' : ℝ) : ℂ) * e + (r' : ℂ) * (e - e') := by
    simp only [cylInf, ccwLoop, ← hr, ← hr', ← he, ← he']
    push_cast; ring
  have hen : ‖e‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have he'n : ‖e'‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hee : ‖e - e'‖ ≤ 2 * π * |t - t'| := by
    have h1 : e - e' = e' * (Complex.exp (((2 * π * (t - t') : ℝ) : ℂ) * Complex.I) - 1) := by
      rw [mul_sub, mul_one, he, he', ← Complex.exp_add]
      congr 2
      push_cast; ring
    rw [h1, norm_mul, he'n, one_mul]
    have h2 := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * π * (t - t'))
    have h3 : ((2 * π * (t - t') : ℝ) : ℂ) * Complex.I =
        Complex.I * ((2 * π * (t - t') : ℝ) : ℂ) := by ring
    rw [h3]
    refine h2.trans ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  have hrr : |r - r'| ≤ (r + r') * (2 * π * |s - s'|) := by
    have := emb_abs_exp_sub_le (2 * π * s) (2 * π * s')
    rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at this
    exact this
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, hen, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos hr'pos]
  have hpi : 0 ≤ 2 * π * |t - t'| := by positivity
  have h4 : r' * ‖e - e'‖ ≤ r' * (2 * π * |t - t'|) := by gcongr
  have h5 : r' * (2 * π * |t - t'|) ≤ (r + r') * (2 * π * |t - t'|) := by
    have : r' ≤ r + r' := by linarith
    gcongr
  calc |r - r'| + r' * ‖e - e'‖ ≤ (r + r') * (2 * π * |s - s'|) + (r + r') * (2 * π * |t - t'|) := by
        linarith
    _ = _ := by ring

theorem emb_eventually_le (C b ε : ℝ) (hb : 0 < b) (hε : 0 < ε) :
    ∃ s₀ : ℝ, ∀ s ≥ s₀, C * Real.exp (-(b * s)) ≤ ε := by
  have h : Tendsto (fun s : ℝ => C * Real.exp (-(b * s))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => -(b * s)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hb)
    simpa using (Real.tendsto_exp_atBot.comp h1).const_mul C
  obtain ⟨s₀, hs₀⟩ := eventually_atTop.mp (h.eventually (ge_mem_nhds hε))
  exact ⟨s₀, hs₀⟩

/-- Let `u` converge exponentially fast in `C^∞` to the trivial cylinder over `P` at `∞`, and let
`x` satisfy `c₀ |τ - τ'| ≤ ‖x τ - x τ'‖` for `|τ - τ'| ≤ T / 2`. Then outside some ball the
symplectization coordinates of `u` satisfy a lower Lipschitz bound in the scale `1 + ‖z‖ + ‖z'‖`. -/
theorem exists_mul_norm_sub_le_of_hasExpAsymptoticsEnd_aux {n : ℕ} (H : V n → ℝ) (u : ℂ → V n)
    (P : ReebOrbit H) (b : ℝ) (hb : 0 < b) (hexp : HasExpAsymptoticsEnd H u cylInf P 1 b)
    (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hsep : ∀ τ τ' : ℝ, |τ - τ'| ≤ P.T / 2 → c₀ * |τ - τ'| ≤ ‖P.x τ - P.x τ'‖) :
    ∃ c > 0, ∃ R > 0, ∀ z z' : ℂ, R ≤ ‖z‖ → R ≤ ‖z'‖ →
      c * ‖z - z'‖ ≤ (1 + ‖z‖ + ‖z'‖) *
        (|aCoord H (u z) - aCoord H (u z')| + ‖proj H (u z) - proj H (u z')‖) := by
  obtain ⟨d, c', ⟨⟨s₁, hsm1⟩, ha⟩, ⟨⟨s₂, hsm2⟩, hw⟩⟩ := hexp
  obtain ⟨Ca, sa, hCa⟩ := ha 1
  obtain ⟨Cw, sw, hCw⟩ := hw 1
  have hT := P.T_pos
  set κ : ℝ := min P.T (c₀ * P.T) with hκ
  have hκpos : 0 < κ := lt_min hT (by positivity)
  set η : ℝ := κ / 4 with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨s₃, hs₃⟩ := emb_eventually_le Ca b η hb hηpos
  obtain ⟨s₄, hs₄⟩ := emb_eventually_le Cw b η hb hηpos
  set S₀ : ℝ := max (max (s₁ + 1) (s₂ + 1)) (max (max sa sw) (max s₃ s₄)) with hS₀
  have hS1 : s₁ + 1 ≤ S₀ := (le_max_left _ _).trans (le_max_left _ _)
  have hS2 : s₂ + 1 ≤ S₀ := (le_max_right _ _).trans (le_max_left _ _)
  have hSa : sa ≤ S₀ :=
    (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hSw : sw ≤ S₀ :=
    (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hS3 : s₃ ≤ S₀ :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hS4 : s₄ ≤ S₀ :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  set Sset : Set (ℝ × ℝ) := {p | S₀ ≤ p.1} with hSset
  have hconv : Convex ℝ Sset := by
    have : Sset = (Prod.fst : ℝ × ℝ → ℝ) ⁻¹' Set.Ici S₀ := rfl
    rw [this]
    exact (convex_Ici S₀).linear_preimage (LinearMap.fst ℝ ℝ ℝ)
  set α : ℝ × ℝ → ℝ := fun p => endA H u cylInf p - 1 * P.T * p.1 - d with hα
  set β : ℝ × ℝ → V n := fun p => endW H u cylInf p - P.x (1 * P.T * p.2 + c') with hβ
  have hαd : ∀ p ∈ Sset, DifferentiableAt ℝ α p := by
    intro p hp
    have hmem : Set.Ioi s₁ ×ˢ (Set.univ : Set ℝ) ∈ 𝓝 p :=
      (isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨by
        have : S₀ ≤ p.1 := hp
        show s₁ < p.1
        linarith, Set.mem_univ _⟩
    exact (hsm1.contDiffAt hmem).differentiableAt (by simp)
  have hβd : ∀ p ∈ Sset, DifferentiableAt ℝ β p := by
    intro p hp
    have hmem : Set.Ioi s₂ ×ˢ (Set.univ : Set ℝ) ∈ 𝓝 p :=
      (isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨by
        have : S₀ ≤ p.1 := hp
        show s₂ < p.1
        linarith, Set.mem_univ _⟩
    exact (hsm2.contDiffAt hmem).differentiableAt (by simp)
  have hαb : ∀ p ∈ Sset, ‖fderiv ℝ α p‖ ≤ η := by
    rintro ⟨s, t⟩ hp
    have hp' : S₀ ≤ s := hp
    have h1 := hCa s (hSa.trans hp') t
    rw [norm_iteratedFDeriv_one] at h1
    exact h1.trans (hs₃ s (hS3.trans hp'))
  have hβb : ∀ p ∈ Sset, ‖fderiv ℝ β p‖ ≤ η := by
    rintro ⟨s, t⟩ hp
    have hp' : S₀ ≤ s := hp
    have h1 := hCw s (hSw.trans hp') t
    rw [norm_iteratedFDeriv_one] at h1
    exact h1.trans (hs₄ s (hS4.trans hp'))
  -- the key inequality in cylinder coordinates
  have hkey : ∀ s s' t t' : ℝ, S₀ ≤ s → S₀ ≤ s' → |t - t'| ≤ 1 / 2 →
      κ / 2 * max |s - s'| |t - t'| ≤
        |endA H u cylInf (s, t) - endA H u cylInf (s', t')| +
          ‖endW H u cylInf (s, t) - endW H u cylInf (s', t')‖ := by
    intro s s' t t' hs hs' ht
    have hpn : ‖((s', t') : ℝ × ℝ) - (s, t)‖ = max |s - s'| |t - t'| := by
      rw [Prod.norm_def]
      simp [Real.norm_eq_abs, abs_sub_comm]
    have h1 := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := α) hαd hαb hconv
      (show ((s', t') : ℝ × ℝ) ∈ Sset from hs') (show ((s, t) : ℝ × ℝ) ∈ Sset from hs)
    have h2 := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := β) hβd hβb hconv
      (show ((s', t') : ℝ × ℝ) ∈ Sset from hs') (show ((s, t) : ℝ × ℝ) ∈ Sset from hs)
    rw [show ((s, t) : ℝ × ℝ) - (s', t') = -(((s', t') : ℝ × ℝ) - (s, t)) by
      ext <;> simp, norm_neg, hpn] at h1 h2
    set m : ℝ := max |s - s'| |t - t'| with hm
    -- `a`-component
    have hA : P.T * |s - s'| ≤
        |endA H u cylInf (s, t) - endA H u cylInf (s', t')| + η * m := by
      have e : P.T * (s - s') = (endA H u cylInf (s, t) - endA H u cylInf (s', t')) -
          (α (s, t) - α (s', t')) := by
        simp only [hα]; ring
      have h3 : |P.T * (s - s')| ≤ |endA H u cylInf (s, t) - endA H u cylInf (s', t')| +
          |α (s, t) - α (s', t')| := by
        rw [e]; exact abs_sub _ _
      rw [abs_mul, abs_of_pos hT] at h3
      rw [Real.norm_eq_abs] at h1
      linarith
    -- `w`-component
    have hW : c₀ * (P.T * |t - t'|) ≤
        ‖endW H u cylInf (s, t) - endW H u cylInf (s', t')‖ + η * m := by
      have hτ : |(1 * P.T * t + c') - (1 * P.T * t' + c')| = P.T * |t - t'| := by
        rw [show (1 * P.T * t + c') - (1 * P.T * t' + c') = P.T * (t - t') by ring, abs_mul,
          abs_of_pos hT]
      have h4 := hsep (1 * P.T * t + c') (1 * P.T * t' + c') (by
        rw [hτ]; nlinarith)
      rw [hτ] at h4
      have e : P.x (1 * P.T * t + c') - P.x (1 * P.T * t' + c') =
          (endW H u cylInf (s, t) - endW H u cylInf (s', t')) - (β (s, t) - β (s', t')) := by
        simp only [hβ]; abel
      rw [e] at h4
      have h5 := norm_sub_le (endW H u cylInf (s, t) - endW H u cylInf (s', t'))
        (β (s, t) - β (s', t'))
      linarith
    have hκ1 : κ ≤ P.T := min_le_left _ _
    have hκ2 : κ ≤ c₀ * P.T := min_le_right _ _
    have hm0 : 0 ≤ m := le_max_of_le_left (abs_nonneg _)
    have hmain : κ * m ≤ P.T * |s - s'| + c₀ * (P.T * |t - t'|) := by
      have h6 : 0 ≤ P.T * |s - s'| := by positivity
      have h7 : 0 ≤ c₀ * (P.T * |t - t'|) := by positivity
      rcases max_cases |s - s'| |t - t'| with ⟨h8, -⟩ | ⟨h8, -⟩
      · rw [hm, h8]
        have : κ * |s - s'| ≤ P.T * |s - s'| := by gcongr
        linarith
      · rw [hm, h8]
        have : κ * |t - t'| ≤ c₀ * P.T * |t - t'| := by gcongr
        have e : c₀ * P.T * |t - t'| = c₀ * (P.T * |t - t'|) := by ring
        linarith
    have hηm : η * m = κ / 4 * m := rfl
    linarith
  -- conclusion
  have h2pi : (0 : ℝ) < 2 * π := by positivity
  refine ⟨κ / (8 * π), by positivity, Real.exp (2 * π * S₀), Real.exp_pos _, ?_⟩
  intro z z' hz hz'
  have hzpos : 0 < ‖z‖ := (Real.exp_pos _).trans_le hz
  have hz'pos : 0 < ‖z'‖ := (Real.exp_pos _).trans_le hz'
  have hz0 : z ≠ 0 := norm_pos_iff.1 hzpos
  have hz'0 : z' ≠ 0 := norm_pos_iff.1 hz'pos
  obtain ⟨t, ht⟩ := emb_exists_cylInf_eq z hz0
  obtain ⟨t₀, ht₀⟩ := emb_exists_cylInf_eq z' hz'0
  set s : ℝ := Real.log ‖z‖ / (2 * π) with hs
  set s' : ℝ := Real.log ‖z'‖ / (2 * π) with hs'
  have hss : S₀ ≤ s := by
    rw [hs, le_div_iff₀ h2pi, Real.le_log_iff_exp_le hzpos, mul_comm]; exact hz
  have hss' : S₀ ≤ s' := by
    rw [hs', le_div_iff₀ h2pi, Real.le_log_iff_exp_le hz'pos, mul_comm]; exact hz'
  set k : ℤ := round (t - t₀) with hk
  set t' : ℝ := t₀ + k with ht'def
  have ht' : cylInf s' t' = z' := by rw [ht'def, emb_cylInf_add_int, ht₀]
  have htt : |t - t'| ≤ 1 / 2 := by
    have := abs_sub_round (t - t₀)
    rw [ht'def, show t - (t₀ + (k : ℝ)) = t - t₀ - k by ring]
    exact this
  have hkk := hkey s s' t t' hss hss' htt
  have hA1 : endA H u cylInf (s, t) = aCoord H (u z) := by simp only [endA, ht]
  have hA2 : endA H u cylInf (s', t') = aCoord H (u z') := by simp only [endA, ht']
  have hW1 : endW H u cylInf (s, t) = proj H (u z) := by simp only [endW, ht]
  have hW2 : endW H u cylInf (s', t') = proj H (u z') := by simp only [endW, ht']
  rw [hA1, hA2, hW1, hW2] at hkk
  have hdist := emb_norm_cylInf_sub_le s s' t t'
  rw [ht, ht', ← emb_norm_cylInf s t, ← emb_norm_cylInf s' t', ht, ht'] at hdist
  set m : ℝ := max |s - s'| |t - t'| with hm
  have hm0 : 0 ≤ m := le_max_of_le_left (abs_nonneg _)
  have hm1 : |s - s'| + |t - t'| ≤ 2 * m := by
    have := le_max_left |s - s'| |t - t'|
    have := le_max_right |s - s'| |t - t'|
    linarith
  set Δ : ℝ := |aCoord H (u z) - aCoord H (u z')| + ‖proj H (u z) - proj H (u z')‖ with hΔ
  have hΔ0 : 0 ≤ Δ := by positivity
  set Sc : ℝ := 1 + ‖z‖ + ‖z'‖ with hSc
  have hScpos : 0 < Sc := by positivity
  have hd2 : ‖z - z'‖ ≤ Sc * (4 * π * m) := by
    refine hdist.trans ?_
    have h1 : ‖z‖ + ‖z'‖ ≤ Sc := by rw [hSc]; linarith
    have h2 : 2 * π * (|s - s'| + |t - t'|) ≤ 4 * π * m := by
      have : 2 * π * (|s - s'| + |t - t'|) ≤ 2 * π * (2 * m) := by gcongr
      linarith
    have h3 : 0 ≤ 2 * π * (|s - s'| + |t - t'|) := by positivity
    calc _ ≤ Sc * (2 * π * (|s - s'| + |t - t'|)) := by gcongr
      _ ≤ _ := by gcongr
  have hpi : 0 < π := Real.pi_pos
  calc κ / (8 * π) * ‖z - z'‖ ≤ κ / (8 * π) * (Sc * (4 * π * m)) := by gcongr
    _ = Sc * (κ / 2 * m) := by field_simp; ring
    _ ≤ Sc * Δ := by gcongr

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (u : ℂ → V n)
    (P : ReebOrbit H) (b : ℝ) (hb : 0 < b) (hexp : HasExpAsymptoticsEnd H u cylInf P 1 b)
    (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hsep : ∀ τ τ' : ℝ, |τ - τ'| ≤ P.T / 2 → c₀ * |τ - τ'| ≤ ‖P.x τ - P.x τ'‖) :
    ∃ c > 0, ∃ R > 0, ∀ z z' : ℂ, R ≤ ‖z‖ → R ≤ ‖z'‖ →
      c * ‖z - z'‖ ≤ (1 + ‖z‖ + ‖z'‖) *
        (|aCoord H (u z) - aCoord H (u z')| + ‖proj H (u z) - proj H (u z')‖) :=
  exists_mul_norm_sub_le_of_hasExpAsymptoticsEnd_aux H u P b hb hexp c₀ hc₀ hsep
