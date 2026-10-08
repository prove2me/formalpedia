-- Prove2me | solution 1 for BartlettNN.Margin.theorem2_margin_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T13:12:10.930293+00:00
-- url     : https://prove2.me/submissions/5c193b61-ff2e-4c6f-8ed4-0e979692706e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BartlettNN_Margin_Classification
import Definitions.Def_BartlettNN_Margin_FatShattering
import Definitions.Def_BartlettNN_Margin_Squash
import Definitions.Def_BartlettNN_Margin_Covering
import Theorems.Thm_BartlettNN_Margin_lemma4_covering_margin_bound
import Theorems.Thm_BartlettNN_Margin_log_Ninf_squash_lt
import Theorems.Thm_BartlettNN_Margin_fat_squash_le_fat

set_option autoImplicit false

open MeasureTheory

namespace BartlettNN.Margin

theorem r967_Ninf_le_one {X : Type*} (F : Set (X → ℝ)) (γ : ℝ) (hγ : 0 < γ) (m : ℕ)
    (h0 : fat F (γ / 16) = 0) : Ninf F (γ / 2) m ≤ 1 := by
  have hclose : ∀ f ∈ F, ∀ g ∈ F, ∀ x : X, f x - g x < γ / 8 := by
    intro f hf g hg x
    by_contra hcon
    push_neg at hcon
    have hsh : GammaShatters F (γ / 16) (fun _ : Fin 1 => x) := by
      refine ⟨fun _ => (f x + g x) / 2, fun b => ?_⟩
      cases hb : b 0
      · refine ⟨g, hg, fun i => ?_⟩
        have hi : i = 0 := Subsingleton.elim _ _
        subst hi
        simp only [hb, pm]
        norm_num
        linarith
      · refine ⟨f, hf, fun i => ?_⟩
        have hi : i = 0 := Subsingleton.elim _ _
        subst hi
        simp only [hb, pm]
        norm_num
        linarith
    have hle : ((1 : ℕ) : ℕ∞) ≤ fat F (γ / 16) := by
      unfold fat
      exact le_iSup_of_le 1 (le_iSup_of_le (fun _ : Fin 1 => x) (le_iSup_of_le hsh le_rfl))
    rw [h0] at hle
    simp at hle
  unfold Ninf
  refine iSup_le fun x => ?_
  rcases F.eq_empty_or_nonempty with hF | ⟨f0, hf0⟩
  · unfold coverNum
    refine iInf_le_of_le ∅ (iInf_le_of_le (by simp [hF]) ?_)
    simp
  · unfold coverNum
    refine iInf_le_of_le {f0} (iInf_le_of_le ?_ ?_)
    · intro f hf
      refine ⟨f0, Finset.mem_singleton_self _, ?_⟩
      unfold dInf
      have hb : (⨆ i, |f0 (x i) - f (x i)|) ≤ γ / 8 := by
        refine Real.iSup_le (fun i => ?_) (by positivity)
        rw [abs_le]
        constructor
        · have := hclose f hf f0 hf0 (x i); linarith
        · have := hclose f0 hf0 f hf (x i); linarith
      linarith
    · simp

end BartlettNN.Margin

section

open BartlettNN.Margin

theorem solution {X : Type*} [MeasurableSpace X]
    (P : Measure (X × Bool)) [IsProbabilityMeasure P] (H : Set (X → ℝ))
    (γ δ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2)
    (m d : ℕ) (hm : 1 ≤ m) (hd : fat H (γ / 16) = d) (hd34 : d ≤ 34 * m)
    (hHmeas : ∀ h ∈ H, Measurable h)
    (hbad : ∀ ε : ℝ, MeasurableSet {z : Fin m → X × Bool | ∃ h ∈ H, erHat γ z h + ε ≤ er P h})
    (hghost : ∀ ε : ℝ, MeasurableSet {w : Fin (m + m) → X × Bool | ∃ h ∈ H,
      ((Finset.univ.filter fun i : Fin m =>
          γ ≤ |squash γ (h (w (Fin.natAdd m i)).1) - γ * pm (w (Fin.natAdd m i)).2|).card : ℝ) / m
        ≥ ((Finset.univ.filter fun i : Fin m =>
          squash γ (h (w (Fin.castAdd m i)).1) ≠ γ * pm (w (Fin.castAdd m i)).2).card : ℝ) / m
          + ε / 2}) :
    Measure.pi (fun _ : Fin m => P)
      {z | ∃ h ∈ H, erHat γ z h + Real.sqrt ((2 / m) *
          (d * Real.log (34 * Real.exp 1 * m / d) * Real.logb 2 (578 * m) + Real.log (4 / δ)))
        ≤ er P h}
      ≤ ENNReal.ofReal δ := by
  classical
  have hfatS : fat (squashClass γ H) (γ / 16) ≤ d := (fat_squash_le_fat H γ hγ0).trans hd.le
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2v := Real.log_two_gt_d9
  have h4δ : 8 < 4 / δ := by rw [lt_div_iff₀ hδ0]; linarith
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hδ4 : 3 * Real.log 2 < Real.log (4 / δ) := by
    rw [← hlog8]; exact Real.log_lt_log (by norm_num) h4δ
  have hK : 9 < Real.logb 2 (578 * m) := by
    have h512 : Real.log 512 = 9 * Real.log 2 := by
      rw [show (512 : ℝ) = 2 ^ 9 by norm_num, Real.log_pow]; norm_num
    have : 9 * Real.log 2 < Real.log (578 * m) := by
      rw [← h512]; exact Real.log_lt_log (by norm_num) (by nlinarith)
    rw [Real.logb, lt_div_iff₀ hl2]; linarith
  have key : ∀ N : ℕ, Ninf (squashClass γ H) (γ / 2) (2 * m) ≤ N →
      Real.log (2 * N / δ) ≤
        d * Real.log (34 * Real.exp 1 * m / d) * Real.logb 2 (578 * m) + Real.log (4 / δ) →
      Measure.pi (fun _ : Fin m => P)
        {z | ∃ h ∈ H, erHat γ z h + Real.sqrt ((2 / m) *
            (d * Real.log (34 * Real.exp 1 * m / d) * Real.logb 2 (578 * m) + Real.log (4 / δ)))
          ≤ er P h}
        ≤ ENNReal.ofReal δ := by
    intro N hN hlog
    refine le_trans (measure_mono ?_)
      (lemma4_covering_margin_bound P H γ δ hγ0 hδ0 hδ1 m hm hHmeas hbad hghost N hN)
    intro z hz
    obtain ⟨h, hH, hle⟩ := hz
    refine ⟨h, hH, le_trans ?_ hle⟩
    have hm0 : (0 : ℝ) ≤ 2 / m := by positivity
    have hs := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hlog hm0)
    linarith
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · subst hd0
    have h0 : fat (squashClass γ H) (γ / 16) = 0 := by
      have := hfatS; simp at this; exact this
    refine key 1 (by simpa using r967_Ninf_le_one _ γ hγ0 (2 * m) h0) ?_
    simp only [Nat.cast_zero, zero_mul, zero_add, Nat.cast_one, mul_one]
    exact Real.log_le_log (by positivity) (by gcongr; norm_num)
  · have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hdpos
    have hd34R : (d : ℝ) ≤ 34 * m := by exact_mod_cast hd34
    set x : ℝ := 34 * Real.exp 1 * m / d with hx
    set L : ℝ := Real.logb 2 x with hL
    set K : ℝ := Real.logb 2 (578 * m) with hKdef
    have hlogx : Real.log x = L * Real.log 2 := by
      rw [hL, Real.logb, div_mul_cancel₀ _ hl2.ne']
    have he := Real.exp_one_gt_d9
    have hx2 : 2 ≤ x := by
      rw [hx, le_div_iff₀ (by positivity)]; nlinarith
    have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    by_cases hbig : (d : ℝ) * L + 1 ≤ m
    · have hL1 : 1 ≤ L := by
        have h2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx2
        rw [hlogx] at h2; nlinarith
      have hd2m : d ≤ 2 * m := by
        have : (d : ℝ) ≤ 2 * m := by nlinarith
        exact_mod_cast this
      obtain ⟨hfin, hlt⟩ := log_Ninf_squash_lt H γ hγ0 m d hdpos hd2m hfatS hbig
      refine key (Ninf (squashClass γ H) (γ / 2) (2 * m)).toNat
        (ENat.natCast_toNat hfin.ne).ge ?_
      set N := (Ninf (squashClass γ H) (γ / 2) (2 * m)).toNat with hN
      have hdx : (d : ℝ) * Real.log x * K = d * L * K * Real.log 2 := by rw [hlogx]; ring
      rw [hdx]
      rcases Nat.eq_zero_or_pos N with hN0 | hNpos
      · rw [hN0]; simp only [Nat.cast_zero, mul_zero, zero_div, Real.log_zero]
        have : 0 ≤ (d : ℝ) * L * K * Real.log 2 := by
          have : 0 ≤ (d : ℝ) * L := by nlinarith
          have : 0 ≤ (d : ℝ) * L * K := by nlinarith
          nlinarith
        linarith
      · have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
        have hlogN : Real.log N < Real.log 2 + d * L * K * Real.log 2 := by
          have h1 : Real.logb 2 N < 1 + d * L * K := hlt
          rw [Real.logb, div_lt_iff₀ hl2] at h1; linarith
        rw [Real.log_div (by positivity) hδ0.ne', Real.log_mul (by norm_num) hNR.ne',
          Real.log_div (by norm_num) hδ0.ne', hlog4]
        linarith
    · push_neg at hbig
      have hlt1 : 1 < Real.sqrt ((2 / m) *
          (d * Real.log x * K + Real.log (4 / δ))) := by
        rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
        apply Real.sqrt_lt_sqrt (by norm_num)
        have hdL : (m : ℝ) - 1 < d * L := by linarith
        have hdx : (d : ℝ) * Real.log x * K = d * L * K * Real.log 2 := by rw [hlogx]; ring
        rw [hdx]
        have hA : 9 * ((m : ℝ) - 1) ≤ d * L * K := by nlinarith
        have hB : 9 * ((m : ℝ) - 1) * Real.log 2 ≤ d * L * K * Real.log 2 :=
          mul_le_mul_of_nonneg_right hA hl2.le
        rw [div_mul_eq_mul_div, lt_div_iff₀ hmpos]
        nlinarith
      have hempty : {z : Fin m → X × Bool | ∃ h ∈ H, erHat γ z h + Real.sqrt ((2 / m) *
            (d * Real.log x * K + Real.log (4 / δ))) ≤ er P h} = ∅ := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨h, hH, hle⟩
        have her : er P h ≤ 1 := by
          unfold er; exact measureReal_le_one
        have hE : 0 ≤ erHat γ z h := by unfold erHat; positivity
        linarith
      rw [hempty]; simp

end
