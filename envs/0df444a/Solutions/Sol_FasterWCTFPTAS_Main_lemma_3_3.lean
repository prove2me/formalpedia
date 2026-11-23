-- Prove2me | solution 1 for FasterWCTFPTAS.Main.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:34:21.436797+00:00
-- url     : https://prove2.me/submissions/4f90c3db-afdd-4997-b114-17f9345514e0

import Mathlib
import Definitions.Def_FasterWCTFPTAS_Main_Geometry

set_option autoImplicit false

open FasterWCTFPTAS.Main

namespace Lemma33Aux

lemma dotm_abs_bound {m : ℕ} {A X : ℝ} {s : Pt m} {x : Fin (m - 1) → ℝ}
    (hs : ∀ k, 0 ≤ s.1 k ∧ s.1 k ≤ A) (hx : ∀ k, |x k| ≤ X) :
    -(((m - 1 : ℕ) : ℝ) * (A * X)) ≤ dotm s.1 x ∧
      dotm s.1 x ≤ ((m - 1 : ℕ) : ℝ) * (A * X) := by
  unfold dotm
  have hterm : ∀ k : Fin (m - 1), -(A * X) ≤ s.1 k * x k ∧ s.1 k * x k ≤ A * X := by
    intro k
    have hsk : |s.1 k| ≤ A := by
      rw [abs_of_nonneg (hs k).1]
      exact (hs k).2
    have hmul : |s.1 k * x k| ≤ A * X := by
      rw [abs_mul]
      exact mul_le_mul hsk (hx k) (abs_nonneg _) (le_trans (hs k).1 (hs k).2)
    exact abs_le.mp hmul
  constructor
  · calc
      -(((m - 1 : ℕ) : ℝ) * (A * X))
          = ∑ _k : Fin (m - 1), -(A * X) := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ k : Fin (m - 1), s.1 k * x k :=
            Finset.sum_le_sum fun k _ => (hterm k).1
  · calc
      ∑ k : Fin (m - 1), s.1 k * x k
          ≤ ∑ _k : Fin (m - 1), (A * X) :=
            Finset.sum_le_sum fun k _ => (hterm k).2
      _ = ((m - 1 : ℕ) : ℝ) * (A * X) := by
            simp [Finset.sum_const, nsmul_eq_mul]

end Lemma33Aux

theorem solution {m : ℕ} (hm : 2 ≤ m) (δ A B X : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hX : 0 ≤ X) (D : Set (Pt m))
    (hbox : ∀ s ∈ D, InBox A B s) (Q : Set (Pt m)) (hQ : IsKernel (δ / (2 * m)) Q D) :
    IsRelaxedRep δ A B X Q D := by
  refine ⟨hQ.1, fun x hx a haD => ?_⟩
  have hD_ne : D.Nonempty := ⟨a, haD⟩
  have hQ_ne : Q.Nonempty := hQ.2.1 hD_ne
  let v : Pt m := (x, 1)
  have hv0 : v ≠ 0 := by
    intro hv
    have h2 : v.2 = (0 : Pt m).2 := congrArg Prod.snd hv
    norm_num [v] at h2
  have hip_vv : 1 ≤ ip v v := by
    unfold ip dotm
    have hsum : 0 ≤ ∑ k : Fin (m - 1), x k * x k :=
      Finset.sum_nonneg fun k _ => mul_self_nonneg (x k)
    change 1 ≤ (∑ k : Fin (m - 1), x k * x k) + 1 * 1
    linarith
  have hnorm_pos : 0 < norm2 v := by
    unfold norm2
    exact Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one hip_vv)
  have hip_eq : ∀ s : Pt m, ip s v = dotm s.1 x + s.2 := by
    intro s
    simp [ip, v]
  have hAXB_nonneg : 0 ≤ A * X + B := by
    nlinarith
  by_cases hAXB0 : A * X + B = 0
  · obtain ⟨e, heQ⟩ := hQ_ne
    have hAX0 : A * X = 0 := by nlinarith
    have hB0 : B = 0 := by nlinarith
    have hzero : ∀ s ∈ D, dotm s.1 x + s.2 = 0 := by
      intro s hsD
      have hbs := hbox s hsD
      have hd := Lemma33Aux.dotm_abs_bound hbs.1 hx
      rw [hAX0, mul_zero] at hd
      have hs2_lo : 0 ≤ s.2 := hbs.2.1
      have hs2_hi : s.2 ≤ B := hbs.2.2
      linarith
    refine ⟨e, heQ, ?_⟩
    rw [hzero e (hQ.1 heQ), hzero a haD, hAXB0]
    ring_nf
    exact le_rfl
  · have hAXB_pos : 0 < A * X + B := lt_of_le_of_ne hAXB_nonneg (Ne.symm hAXB0)
    let L : ℝ := -(((m - 1 : ℕ) : ℝ) * (A * X))
    let Ubd : ℝ := ((m - 1 : ℕ) : ℝ) * (A * X) + B
    let g : Pt m → ℝ := fun s => ip s v / norm2 v
    have hg_bounds : ∀ s ∈ D, L / norm2 v ≤ g s ∧ g s ≤ Ubd / norm2 v := by
      intro s hsD
      have hbs := hbox s hsD
      have hd := Lemma33Aux.dotm_abs_bound hbs.1 hx
      have hip_lo : L ≤ ip s v := by
        rw [hip_eq]
        linarith [hbs.2.1]
      have hip_hi : ip s v ≤ Ubd := by
        rw [hip_eq]
        linarith [hbs.2.2]
      exact ⟨div_le_div_of_nonneg_right hip_lo (le_of_lt hnorm_pos),
             div_le_div_of_nonneg_right hip_hi (le_of_lt hnorm_pos)⟩
    have hbddAbove_D : BddAbove (g '' D) := by
      refine ⟨Ubd / norm2 v, ?_⟩
      rintro _ ⟨s, hsD, rfl⟩
      exact (hg_bounds s hsD).2
    have hbddBelow_D : BddBelow (g '' D) := by
      refine ⟨L / norm2 v, ?_⟩
      rintro _ ⟨s, hsD, rfl⟩
      exact (hg_bounds s hsD).1
    have hbddBelow_Q : BddBelow (g '' Q) := hbddBelow_D.mono (Set.image_mono hQ.1)
    have hsSup_Q_le_D : sSup (g '' Q) ≤ sSup (g '' D) :=
      csSup_le_csSup hbddAbove_D (hQ_ne.image g) (Set.image_mono hQ.1)
    have hsSup_D_le : sSup (g '' D) ≤ Ubd / norm2 v := by
      refine csSup_le (hD_ne.image g) ?_
      rintro _ ⟨s, hsD, rfl⟩
      exact (hg_bounds s hsD).2
    have hsInf_D_ge : L / norm2 v ≤ sInf (g '' D) := by
      refine le_csInf (hD_ne.image g) ?_
      rintro _ ⟨s, hsD, rfl⟩
      exact (hg_bounds s hsD).1
    have hsInf_D_le_ga : sInf (g '' D) ≤ g a :=
      csInf_le hbddBelow_D ⟨a, haD, rfl⟩
    have hker : (1 - δ / (2 * (m : ℝ))) * width v D ≤ width v Q := hQ.2.2 v hv0
    unfold width at hker
    change (1 - δ / (2 * (m : ℝ))) * (sSup (g '' D) - sInf (g '' D)) ≤
        sSup (g '' Q) - sInf (g '' Q) at hker
    have hm_pos : (0 : ℝ) < (m : ℝ) := by
      have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    have hε_pos : 0 < δ / (2 * (m : ℝ)) := by positivity
    have hε_lt1 : δ / (2 * (m : ℝ)) < 1 := by
      rw [div_lt_one (by linarith)]
      have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    have hsInf_Q_le :
        sInf (g '' Q) ≤ g a + (δ / (2 * (m : ℝ))) * ((Ubd - L) / norm2 v) := by
      have hdiff : sSup (g '' D) - sInf (g '' D) ≤ (Ubd - L) / norm2 v := by
        rw [sub_div]
        linarith
      have h1 : sInf (g '' Q) ≤
          sInf (g '' D) + (δ / (2 * (m : ℝ))) * (sSup (g '' D) - sInf (g '' D)) := by
        linarith
      have h2 : (δ / (2 * (m : ℝ))) * (sSup (g '' D) - sInf (g '' D)) ≤
          (δ / (2 * (m : ℝ))) * ((Ubd - L) / norm2 v) :=
        mul_le_mul_of_nonneg_left hdiff (le_of_lt hε_pos)
      linarith
    have hm_sub : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      have hm1 : 1 ≤ m := by omega
      simpa using (Nat.cast_sub hm1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - (1 : ℕ))
    have hUbd_sub_L : Ubd - L < 2 * (m : ℝ) * (A * X + B) := by
      dsimp [Ubd, L]
      rw [hm_sub]
      have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have hAX_nonneg : 0 ≤ A * X := mul_nonneg hA hX
      nlinarith
    have hstrict :
        (δ / (2 * (m : ℝ))) * ((Ubd - L) / norm2 v) <
          (δ * (A * X + B)) / norm2 v := by
      have h1 : (Ubd - L) / norm2 v < (2 * (m : ℝ) * (A * X + B)) / norm2 v :=
        div_lt_div_of_pos_right hUbd_sub_L hnorm_pos
      have h2 : (δ / (2 * (m : ℝ))) * ((Ubd - L) / norm2 v) <
          (δ / (2 * (m : ℝ))) * ((2 * (m : ℝ) * (A * X + B)) / norm2 v) :=
        mul_lt_mul_of_pos_left h1 hε_pos
      have h3 : (δ / (2 * (m : ℝ))) * ((2 * (m : ℝ) * (A * X + B)) / norm2 v) =
          (δ * (A * X + B)) / norm2 v := by
        field_simp [ne_of_gt hm_pos, ne_of_gt hnorm_pos]
      linarith
    have hsInf_lt : sInf (g '' Q) < (ip a v + δ * (A * X + B)) / norm2 v := by
      have hga : g a + (δ * (A * X + B)) / norm2 v = (ip a v + δ * (A * X + B)) / norm2 v := by
        dsimp [g]
        rw [add_div]
      linarith
    obtain ⟨_, ⟨e, heQ, rfl⟩, he_lt⟩ := exists_lt_of_csInf_lt (hQ_ne.image g) hsInf_lt
    dsimp [g] at he_lt
    have hip_lt : ip e v < ip a v + δ * (A * X + B) :=
      (div_lt_div_iff_of_pos_right hnorm_pos).mp he_lt
    rw [hip_eq e, hip_eq a] at hip_lt
    exact ⟨e, heQ, le_of_lt hip_lt⟩
