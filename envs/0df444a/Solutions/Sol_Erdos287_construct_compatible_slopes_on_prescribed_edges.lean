-- Prove2me | solution 1 for Erdos287.construct_compatible_slopes_on_prescribed_edges
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T12:26:40.268851+00:00
-- url     : https://prove2.me/submissions/35b89540-86dd-4719-9d38-5a6e337c7b63

import Mathlib

open Finset

set_option autoImplicit false
set_option maxHeartbeats 1300000

private def edgeDiff (f : ℕ → ℤ) (e : ℕ × ℕ) : ℤ := f e.2 - f e.1

private def edgeDet (z b : ℕ → ℤ) (e f : ℕ × ℕ) : ℤ :=
  edgeDiff z e * edgeDiff b f - edgeDiff z f * edgeDiff b e

/-- Build a compatible pair on each designated edge, while preserving each
base intercept modulo `K` and allowing arbitrarily large scales and shifts. -/
theorem solution (E : Finset (ℕ × ℕ)) (z b : ℕ → ℤ) (K R T : ℕ)
    (hK : 0 < K)
    (hedge : ∀ e ∈ E, z e.1 < z e.2 ∧ b e.2 ≠ b e.1 ∧ (b e.2 - b e.1) ∣ b e.1)
    (hdet : ∀ e ∈ E, ∀ f ∈ E, e ≠ f →
      (z e.2 - z e.1) * (b f.2 - b f.1) ≠ (z f.2 - z f.1) * (b e.2 - b e.1)) :
    ∃ A C : ℤ, (R : ℤ) < A ∧ (T : ℤ) < C ∧ (K : ℤ) ∣ A ∧ (K : ℤ) ∣ C ∧
      ∀ e ∈ E, 0 < C * (z e.2 - z e.1) + (b e.2 - b e.1) ∧
        (C * (z e.2 - z e.1) + (b e.2 - b e.1)) ∣ A + C * z e.1 + b e.1 := by
  classical
  let P := (K : ℤ) * ∏ e ∈ E, |edgeDiff b e|
  have hP : 0 < P := mul_pos (by exact_mod_cast hK)
    (prod_pos fun e he => abs_pos.mpr (sub_ne_zero.mpr (hedge e he).2.1))
  have hbdP (e : ℕ × ℕ) (he : e ∈ E) : edgeDiff b e ∣ P :=
    dvd_mul_of_dvd_right (((dvd_abs _ _).mpr dvd_rfl).trans
      (dvd_prod_of_mem (fun p => |edgeDiff b p|) he)) _
  let D := ∏ e ∈ E, ∏ f ∈ E, if e = f then 1 else |edgeDet z b e f|
  have hD : 0 < D := prod_pos fun e he => prod_pos fun f hf => by
    by_cases h : e = f
    · simp [h]
    · simpa only [if_neg h, edgeDet, edgeDiff] using
        abs_pos.mpr (sub_ne_zero.mpr (hdet e he f hf h))
  have hdetD (e f : ℕ × ℕ) (he : e ∈ E) (hf : f ∈ E) (hne : e ≠ f) : edgeDet z b e f ∣ D := by
    have h₁ := dvd_prod_of_mem (fun p => if e = p then 1 else |edgeDet z b e p|) hf
    have h₂ := dvd_prod_of_mem (fun p => ∏ f ∈ E, if p = f then 1 else |edgeDet z b p f|) he
    rw [if_neg hne] at h₁
    exact ((dvd_abs _ _).mpr dvd_rfl).trans (h₁.trans h₂)
  let B : ℤ := (T : ℤ) + 1 + ∑ e ∈ E, |edgeDiff b e|
  have hB : 0 < B := by
    have h := sum_nonneg (s := E) (f := fun e => |edgeDiff b e|) (fun _ _ => abs_nonneg _)
    dsimp [B]
    omega
  let C := P * P * (D * B)
  have hCB : B ≤ C := by
    have hpd : 1 ≤ P * P * D := by
      exact one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (by omega) (by omega)) (by omega)
    simpa only [C, mul_assoc, one_mul] using mul_le_mul_of_nonneg_right hpd hB.le
  have hCT : (T : ℤ) < C := by
    have h := sum_nonneg (s := E) (f := fun e => |edgeDiff b e|) (fun _ _ => abs_nonneg _)
    dsimp [B] at hCB
    omega
  have hPC : P ∣ C := dvd_mul_of_dvd_left (dvd_mul_right P P) _
  have hDC : D ∣ C := dvd_mul_of_dvd_right (dvd_mul_right D B) _
  let H (e : ℕ × ℕ) := C * edgeDiff z e + edgeDiff b e
  have hpos (e : ℕ × ℕ) (he : e ∈ E) : 0 < H e := by
    have hzone : 1 ≤ edgeDiff z e := by dsimp [edgeDiff]; have := (hedge e he).1; omega
    have hwall := single_le_sum (f := fun p => |edgeDiff b p|) (fun _ _ => abs_nonneg _) he
    have hCpos := hB.trans_le hCB
    have hprod := mul_le_mul_of_nonneg_left hzone hCpos.le
    rw [mul_one] at hprod
    have habs := neg_abs_le (edgeDiff b e)
    dsimp [H, B] at *
    omega
  let W (e : ℕ × ℕ) := (P / edgeDiff b e) * (D * B) * edgeDiff z e
  let F (e : ℕ × ℕ) := 1 + P * W e
  have hfactor (e : ℕ × ℕ) (he : e ∈ E) : H e = edgeDiff b e * F e := by
    have hdiv : edgeDiff b e * (P / edgeDiff b e) = P := by
      simpa only [mul_comm] using Int.ediv_mul_cancel (hbdP e he)
    dsimp only [H, C, F, W]
    linear_combination -P * (D * B) * edgeDiff z e * hdiv
  have hnonzero (e : ℕ × ℕ) (he : e ∈ E) : (F e).natAbs ≠ 0 := by
    intro h
    have hz := Int.natAbs_eq_zero.mp h
    have hs := hpos e he
    rw [hfactor e he, hz, mul_zero] at hs
    exact (lt_irrefl _ hs)
  have hunit (e : ℕ × ℕ) {n : ℤ} (hp : n ∣ P) (he : n ∣ F e) : n ∣ 1 := by
    simpa [F] using he.sub (dvd_mul_of_dvd_left hp (W e))
  have hPn (e : ℕ × ℕ) : P.natAbs.Coprime (F e).natAbs := by
    apply Nat.coprime_of_dvd
    intro n hp hnP hnF
    exact hp.not_dvd_one (by exact_mod_cast hunit e (Int.natCast_dvd.mpr hnP) (Int.natCast_dvd.mpr hnF))
  have hFF (e f : ℕ × ℕ) (he : e ∈ E) (hf : f ∈ E) (hne : e ≠ f) :
      (F e).natAbs.Coprime (F f).natAbs := by
    apply Nat.coprime_of_dvd
    intro n hp hne' hnf'
    have hneZ := Int.natCast_dvd.mpr hne'
    have hnfZ := Int.natCast_dvd.mpr hnf'
    have hHe : (n : ℤ) ∣ H e := by rw [hfactor e he]; exact dvd_mul_of_dvd_right hneZ _
    have hHf : (n : ℤ) ∣ H f := by rw [hfactor f hf]; exact dvd_mul_of_dvd_right hnfZ _
    have hdet' : (n : ℤ) ∣ edgeDet z b e f := by
      rw [show edgeDet z b e f = edgeDiff z e * H f - edgeDiff z f * H e by
        dsimp [edgeDet, H]; ring]
      exact (dvd_mul_of_dvd_right hHf _).sub (dvd_mul_of_dvd_right hHe _)
    have hCn := (hdet'.trans (hdetD e f he hf hne)).trans hDC
    have hbn : (n : ℤ) ∣ edgeDiff b e := (dvd_add_right (dvd_mul_of_dvd_left hCn _)).mp hHe
    exact hp.not_dvd_one (by exact_mod_cast hunit e (hbn.trans (hbdP e he)) hneZ)
  let edges : Finset (Option (ℕ × ℕ)) := insert none (E.map ⟨some, Option.some_injective _⟩)
  let modulus (e : Option (ℕ × ℕ)) := e.elim P.natAbs (fun p => (F p).natAbs)
  let residue (e : Option (ℕ × ℕ)) : ℤ := e.elim 0 (fun p => -(C * z p.1 + b p.1))
  have hsome (e : ℕ × ℕ) : some e ∈ edges ↔ e ∈ E := by simp [edges]
  have hnone : none ∈ edges := mem_insert_self _ _
  have hm : ∀ e ∈ edges, modulus e ≠ 0 := by
    intro e he
    cases e with
    | none => exact fun h => hP.ne' (Int.natAbs_eq_zero.mp h)
    | some e => exact hnonzero e ((hsome e).mp he)
  have hcop : (edges : Set (Option (ℕ × ℕ))).Pairwise (fun e f => (modulus e).Coprime (modulus f)) := by
    intro e he f hf hne
    cases e <;> cases f
    · exact (hne rfl).elim
    · exact hPn _
    · exact (hPn _).symm
    · exact hFF _ _ ((hsome _).mp he) ((hsome _).mp hf) (fun h => hne (congrArg some h))
  let r (e : Option (ℕ × ℕ)) := (residue e % (modulus e : ℤ)).toNat
  let a := Nat.chineseRemainderOfFinset r modulus edges hm hcop
  let Q := ∏ e ∈ edges, modulus e
  have hQ : 0 < Q := prod_pos fun e he => Nat.pos_of_ne_zero (hm e he)
  let A : ℕ := a + Q * (R + 1)
  have hA : (R : ℤ) < A := by
    have hstep : 1 * (R + 1) ≤ Q * (R + 1) := Nat.mul_le_mul_right (R + 1) hQ
    rw [one_mul] at hstep
    exact_mod_cast (show R < A by dsimp [A]; omega)
  have hmod (e : Option (ℕ × ℕ)) (he : e ∈ edges) : (modulus e : ℤ) ∣ (A : ℤ) - residue e := by
    have hstep : modulus e ∣ Q * (R + 1) := dvd_mul_of_dvd_left (dvd_prod_of_mem modulus he) _
    have hA' : A ≡ r e [MOD modulus e] := by
      simpa only [add_zero] using (a.property e he).add (Nat.modEq_zero_iff_dvd.mpr hstep)
    have hne : (modulus e : ℤ) ≠ 0 := by exact_mod_cast hm e he
    have hr : (r e : ℤ) = residue e % (modulus e : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg _ hne)
    have hres : residue e ≡ (r e : ℤ) [ZMOD (modulus e : ℤ)] := by
      rw [hr]
      simp only [Int.ModEq, Int.emod_emod]
    exact Int.modEq_iff_dvd.mp (hres.trans (Int.modEq_iff_dvd.mpr (Nat.modEq_iff_dvd.mp hA'.symm)))
  have hPA : P ∣ (A : ℤ) := by
    simpa [modulus, residue, Int.natCast_natAbs, abs_dvd] using hmod none hnone
  have hKP : (K : ℤ) ∣ P := dvd_mul_right _ _
  refine ⟨A, C, hA, hCT, hKP.trans hPA, hKP.trans hPC, ?_⟩
  intro e he
  refine ⟨hpos e he, ?_⟩
  let x := (A : ℤ) + C * z e.1 + b e.1
  have hx : edgeDiff b e ∣ x := ((hbdP e he).trans hPA).add
    (dvd_mul_of_dvd_left ((hbdP e he).trans hPC) _) |>.add (hedge e he).2.2
  have hx' : F e ∣ x := by
    have h := hmod (some e) ((hsome e).mpr he)
    rw [show (A : ℤ) - residue (some e) = x by dsimp [residue, x]; ring] at h
    simpa [modulus, Int.natCast_natAbs, abs_dvd] using h
  have hc := (hPn e).coprime_dvd_left (Int.natAbs_dvd_natAbs.mpr (hbdP e he))
  rw [show C * (z e.2 - z e.1) + (b e.2 - b e.1) = H e from rfl, hfactor e he]
  exact Int.natAbs_dvd_natAbs.mp (by
    rw [Int.natAbs_mul]
    exact hc.mul_dvd_of_dvd_of_dvd (Int.natAbs_dvd_natAbs.mpr hx) (Int.natAbs_dvd_natAbs.mpr hx'))

