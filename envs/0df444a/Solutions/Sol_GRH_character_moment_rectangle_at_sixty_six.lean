-- Prove2me | solution 1 for GRH.character_moment_rectangle_at_sixty_six
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T17:21:19.480397+00:00
-- url     : https://prove2.me/submissions/b27a8026-5815-4548-af87-782ba2a4c3c7

import Definitions.Def_GRH_CharacterMoment
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open GRH.CharacterMoment

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

private def U : Finset ℕ := {1, 5, 7, 13, 17, 19, 23, 25, 29, 31, 35, 37, 41, 43, 47, 49, 53, 59, 61, 65}
private def inverseData : Array ℕ := #[0, 1, 0, 0, 0, 53, 0, 19, 0, 0, 0, 0,
  0, 61, 0, 0, 0, 35, 0, 7, 0, 0, 0, 23,
  0, 37, 0, 0, 0, 41, 0, 49, 0, 0, 0, 17,
  0, 25, 0, 0, 0, 29, 0, 43, 0, 0, 0, 59,
  0, 31, 0, 0, 0, 5, 0, 0, 0, 0, 0, 47,
  0, 13, 0, 0, 0, 65]
private def inverse (k : ℕ) : ℕ := read inverseData k

private def rankData : Array ℕ := #[0, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 3,
  3, 4, 4, 4, 4, 5, 5, 6, 6, 6, 6, 7,
  7, 8, 8, 8, 8, 9, 9, 10, 10, 10, 10, 11,
  11, 12, 12, 12, 12, 13, 13, 14, 14, 14, 14, 15,
  15, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 18,
  18, 19, 19, 19, 19, 20]
private def rank (k : ℕ) : ℕ := read rankData k

private def weightData : Array ℕ := #[64, 0, 0, 0, 0, 64, 64, 128, 128, 128, 128, 128,
  128, 192, 192, 192, 192, 256, 256, 294, 294, 294, 294, 314,
  314, 307, 307, 307, 307, 314, 314, 307, 307, 307, 307, 327,
  327, 307, 307, 307, 307, 314, 314, 294, 294, 294, 294, 272,
  272, 294, 294, 294, 294, 256, 256, 256, 256, 256, 256, 192,
  192, 128, 128, 128, 128, 64]
private def weight (k : ℕ) : ℕ := read weightData k

private def centerData : Array ℕ := #[0, 0, 0, 0, 0, 0, 2, 2, 2, 4, 4, 5,
  6, 8, 8, 10, 12, 1, 1, 1, 1]
private def center (k : ℕ) : ℕ := read centerData k

private def upperData : Array ℕ := #[0, 1048576, 573341, 402757, 313492, 258119, 220220, 192552, 171411, 154699, 141135, 129892,
  120412, 112303, 105284, 99144, 93724, 88904, 84586, 80696, 77170, 73959, 71023, 68325,
  65839, 63539, 61406, 59420, 57567, 55834, 54210, 52684, 51247, 49892, 48611, 47399,
  46250, 45160, 44123, 43136, 42195, 41297, 40440, 39619, 38834, 38081, 37359, 36666,
  36000, 35359, 34742, 34148, 33576, 33023, 32490, 31975, 31477, 30995, 30529, 30078,
  29641, 29217, 28807, 28408, 28021, 27645, 27280, 26925, 26580, 26244, 25917, 25599,
  25289, 24987, 24693, 24406, 24126, 23853, 23586, 23326, 23072, 22823, 22581, 22344,
  22112, 21885, 21663, 21446, 21234, 21026, 20822, 20623, 20427, 20236, 20048, 19864,
  19684, 19507, 19334, 19164, 18997, 18833, 18672, 18514, 18359, 18206, 18057, 17910,
  17765, 17623, 17483, 17346, 17211, 17078, 16948, 16819, 16693, 16569, 16446, 16326,
  16207, 16091, 15976, 15863, 15751, 15641, 15533, 15427, 15322, 15218, 15116, 15015,
  14916, 14819, 14722, 14627, 14534, 14441, 14350, 14260, 14171, 14084, 13997, 13912,
  13828, 13745, 13663, 13582, 13502, 13423, 13345, 13268, 13192, 13117, 13042, 12969,
  12897, 12825, 12754, 12684, 12615]
private def upper (k : ℕ) : ℕ := read upperData k

private def r6p2 : Array ℕ := #[0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2,
  0, 4, 0, 0, 0, 2, 0, 1, 0, 0, 0, 2,
  0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2,
  0, 0, 0, 0, 0, 2]
private def r7p2 : Array ℕ := #[0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2,
  0, 4, 0, 0, 0, 4, 0, 1, 0, 0, 0, 4,
  0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0,
  0, 5, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2,
  0, 2, 0, 0, 0, 2]
private def r8p2 : Array ℕ := #[0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2,
  0, 4, 0, 0, 0, 6, 0, 2, 0, 0, 0, 4,
  0, 1, 0, 0, 0, 2, 0, 2, 0, 0, 0, 2,
  0, 5, 0, 0, 0, 2, 0, 0, 0, 0, 0, 4,
  0, 4, 0, 0, 0, 2]
private def r9p2 : Array ℕ := #[0, 3, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0,
  0, 4, 0, 0, 0, 0, 0, 2, 0, 0, 0, 4,
  0, 4, 0, 0, 0, 6, 0, 4, 0, 0, 0, 4,
  0, 1, 0, 0, 0, 2, 0, 2, 0, 0, 0, 4,
  0, 6, 0, 0, 0, 2, 0, 0, 0, 0, 0, 4,
  0, 4, 0, 0, 0, 4]
private def r10p2 : Array ℕ := #[0, 3, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0,
  0, 4, 0, 0, 0, 0, 0, 4, 0, 0, 0, 6,
  0, 4, 0, 0, 0, 6, 0, 4, 0, 0, 0, 4,
  0, 2, 0, 0, 0, 4, 0, 2, 0, 0, 0, 4,
  0, 8, 0, 0, 0, 4, 0, 0, 0, 0, 0, 4,
  0, 6, 0, 0, 0, 6]
private def r11p2 : Array ℕ := #[0, 5, 0, 0, 0, 4, 0, 4, 0, 0, 0, 0,
  0, 6, 0, 0, 0, 2, 0, 4, 0, 0, 0, 6,
  0, 6, 0, 0, 0, 8, 0, 4, 0, 0, 0, 4,
  0, 3, 0, 0, 0, 4, 0, 4, 0, 0, 0, 6,
  0, 8, 0, 0, 0, 4, 0, 0, 0, 0, 0, 6,
  0, 6, 0, 0, 0, 6]
private def r12p2 : Array ℕ := #[0, 7, 0, 0, 0, 4, 0, 4, 0, 0, 0, 0,
  0, 6, 0, 0, 0, 4, 0, 6, 0, 0, 0, 6,
  0, 8, 0, 0, 0, 8, 0, 4, 0, 0, 0, 6,
  0, 3, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6,
  0, 9, 0, 0, 0, 6, 0, 0, 0, 0, 0, 8,
  0, 8, 0, 0, 0, 6]
private def r13p2 : Array ℕ := #[0, 9, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0,
  0, 6, 0, 0, 0, 6, 0, 8, 0, 0, 0, 8,
  0, 8, 0, 0, 0, 8, 0, 5, 0, 0, 0, 8,
  0, 5, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6,
  0, 11, 0, 0, 0, 8, 0, 0, 0, 0, 0, 8,
  0, 8, 0, 0, 0, 8]
private def r14p2 : Array ℕ := #[0, 10, 0, 0, 0, 8, 0, 8, 0, 0, 0, 0,
  0, 8, 0, 0, 0, 8, 0, 10, 0, 0, 0, 8,
  0, 10, 0, 0, 0, 8, 0, 7, 0, 0, 0, 8,
  0, 7, 0, 0, 0, 6, 0, 6, 0, 0, 0, 8,
  0, 11, 0, 0, 0, 10, 0, 0, 0, 0, 0, 10,
  0, 8, 0, 0, 0, 10]
private def r15p2 : Array ℕ := #[0, 10, 0, 0, 0, 10, 0, 10, 0, 0, 0, 0,
  0, 10, 0, 0, 0, 10, 0, 10, 0, 0, 0, 10,
  0, 12, 0, 0, 0, 8, 0, 8, 0, 0, 0, 10,
  0, 9, 0, 0, 0, 8, 0, 8, 0, 0, 0, 8,
  0, 11, 0, 0, 0, 12, 0, 0, 0, 0, 0, 10,
  0, 10, 0, 0, 0, 12]
private def r16p2 : Array ℕ := #[0, 12, 0, 0, 0, 12, 0, 12, 0, 0, 0, 0,
  0, 12, 0, 0, 0, 10, 0, 10, 0, 0, 0, 10,
  0, 13, 0, 0, 0, 10, 0, 10, 0, 0, 0, 12,
  0, 11, 0, 0, 0, 10, 0, 10, 0, 0, 0, 10,
  0, 11, 0, 0, 0, 12, 0, 0, 0, 0, 0, 12,
  0, 12, 0, 0, 0, 14]

private def rowData : Array (List (Array ℕ)) := #[
  [],
  [],
  [],
  [],
  [],
  [],
  [r6p2],
  [r7p2],
  [r8p2],
  [r9p2],
  [r10p2],
  [r11p2],
  [r12p2],
  [r13p2],
  [r14p2],
  [r15p2],
  [r16p2],
  [],
  [],
  [],
  []]
private def rows (r : ℕ) : List (Array ℕ) := (rowData[rank r]?).getD []

private def validAt (r : ℕ) : Prop :=
  r ≠ 0 → Rows 66 U inverse (entry r) (rows r) ∧
   64^(2^(rows r).length) * deviation U (lastRow (entry r) (rows r)) (center (rank r))
     ≤ (weight r)^(2^(rows r).length)

private theorem block0 : ∀ k : Fin 6, validAt (k.val+0) := by
  unfold validAt
  decide +kernel

private theorem block6 : ∀ k : Fin 6, validAt (k.val+6) := by
  unfold validAt
  decide +kernel

private theorem block12 : ∀ k : Fin 6, validAt (k.val+12) := by
  unfold validAt
  decide +kernel

private theorem block18 : ∀ k : Fin 6, validAt (k.val+18) := by
  unfold validAt
  decide +kernel

private theorem block24 : ∀ k : Fin 6, validAt (k.val+24) := by
  unfold validAt
  decide +kernel

private theorem block30 : ∀ k : Fin 6, validAt (k.val+30) := by
  unfold validAt
  decide +kernel

private theorem block36 : ∀ k : Fin 6, validAt (k.val+36) := by
  unfold validAt
  decide +kernel

private theorem block42 : ∀ k : Fin 6, validAt (k.val+42) := by
  unfold validAt
  decide +kernel

private theorem block48 : ∀ k : Fin 6, validAt (k.val+48) := by
  unfold validAt
  decide +kernel

private theorem block54 : ∀ k : Fin 6, validAt (k.val+54) := by
  unfold validAt
  decide +kernel

private theorem block60 : ∀ k : Fin 6, validAt (k.val+60) := by
  unfold validAt
  decide +kernel

private theorem profile : Profile 66 64 weight := by
  refine ⟨U,inverse,rows,(fun r => center (rank r)),?_,?_,by decide,?_⟩
  · decide +kernel
  · unfold Permutes
    decide +kernel
  · rintro ⟨r,hr⟩
    change validAt r
    by_cases h0 : r < 6
    · exact block0 ⟨r,h0⟩
    by_cases h6 : r < 12
    · have h := block6 ⟨r-6,by omega⟩
      simpa only [show r-6+6=r by omega] using h
    by_cases h12 : r < 18
    · have h := block12 ⟨r-12,by omega⟩
      simpa only [show r-12+12=r by omega] using h
    by_cases h18 : r < 24
    · have h := block18 ⟨r-18,by omega⟩
      simpa only [show r-18+18=r by omega] using h
    by_cases h24 : r < 30
    · have h := block24 ⟨r-24,by omega⟩
      simpa only [show r-24+24=r by omega] using h
    by_cases h30 : r < 36
    · have h := block30 ⟨r-30,by omega⟩
      simpa only [show r-30+30=r by omega] using h
    by_cases h36 : r < 42
    · have h := block36 ⟨r-36,by omega⟩
      simpa only [show r-36+36=r by omega] using h
    by_cases h42 : r < 48
    · have h := block42 ⟨r-42,by omega⟩
      simpa only [show r-42+42=r by omega] using h
    by_cases h48 : r < 54
    · have h := block48 ⟨r-48,by omega⟩
      simpa only [show r-48+48=r by omega] using h
    by_cases h54 : r < 60
    · have h := block54 ⟨r-54,by omega⟩
      simpa only [show r-54+54=r by omega] using h
    by_cases h60 : r < 66
    · have h := block60 ⟨r-60,by omega⟩
      simpa only [show r-60+60=r by omega] using h
    omega

/-- A multiplicative convolution certificate gives the closed height-one
rectangle for every conductor dividing 66. -/
theorem solution (d : ℕ) (hd : d ∣ 66) (a b H : ℝ) (ha : (27/31:ℝ) ≤ a)
    (hab : a ≤ b) (hb : b ≤ 7/8) (hH : 0 ≤ H) (hhi : H ≤ 1) : Covers d a b H := by
  refine ⟨66,159,327,1048576,64,27,31,153,100,weight,upper,by decide,hd,by decide,
    by decide,by decide,by decide,by decide,ha,?_,profile,?_,?_,?_⟩
  · have re := mul_self_le_mul_self (show 0 ≤ b by linarith) hb
    have im := mul_self_le_mul_self hH hhi
    nlinarith
  · decide +kernel
  · unfold GRH.DirichletPrefix.Table
    decide +kernel
  · decide +kernel
