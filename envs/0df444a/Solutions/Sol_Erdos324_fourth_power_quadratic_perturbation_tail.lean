-- Prove2me | solution 1 for Erdos324.fourth_power_quadratic_perturbation_tail
-- status  : ACCEPTED   (prove)
-- author  : @Mceppaglia
-- created : 2026-11-20T17:50:55.69574+00:00
-- url     : https://prove2.me/submissions/4b511a95-2b1d-4806-9126-9068615cd3b0

import Mathlib

/-!
# Repeated pair sums in every tail of the family n⁴ + c n²

SPDX-License-Identifier: Apache-2.0

Matt selected the family and directed the investigation. OpenAI Codex developed
the fixed-coefficient construction, found the exceptional seeds and wrote the
Lean formalization. The question is a restriction of Erdős problem 324.
The quartic difference equation appears in T. D. Browning, §3, (3.1).
M. Ulas, Theorem 5.3 (arXiv:0811.2477), gives the case c = -2, which
also yields c = -2h² by dilation. The pure fourth-power collision is classical.
Mathlib's Pell development is by Michael Geißer and Michael Stoll.
-/

namespace Quartic324

def quartic (c n : ℤ) : ℤ := n^4 + c*n^2
def disc (c : ℤ) : ℤ := c^4 + 30*c^3 + 252*c^2 + 680*c

def Tail (c : ℤ) : Prop := ∀ B : ℕ, ∃ a b r s : ℕ,
  B < a ∧ a < b ∧ B < r ∧ r < s ∧ a ≠ r ∧ a ≠ s ∧ b ≠ r ∧ b ≠ s ∧
  quartic c a + quartic c b = quartic c r + quartic c s

end Quartic324

namespace Quartic324
open Polynomial

/-- Eliminate the first Pell coordinate using the line `a x + b y = t`. -/
private noncomputable def linePolynomial (D a b t : ℤ) : Polynomial ℤ :=
  C (b^2 - a^2*D) * X^2 + C (-2*t*b) * X + C (t^2-a^2)

private theorem linePolynomial_nonzero (D a b t : ℤ) (hp : 0 < D)
    (hab : (a,b) ≠ (0,0)) : linePolynomial D a b t ≠ 0 := by
  intro h
  have hz (z : ℤ) : (b^2-a^2*D)*z^2 + (-2*t*b)*z + (t^2-a^2) = 0 := by
    simpa [linePolynomial] using congrArg (fun P : Polynomial ℤ => P.eval z) h
  have hc : t^2 = a^2 := sub_eq_zero.mp (by simpa using hz 0)
  have hlin : t*b = 0 := by nlinarith only [hz 1, hz (-1)]
  have hquad : b^2 = a^2*D := by nlinarith only [hz 1, hz (-1), hc]
  rcases mul_eq_zero.mp hlin with ht | hb
  · rw [ht] at hc
    have ha : a = 0 := by nlinarith
    rw [ha] at hquad
    have hb : b = 0 := by nlinarith
    exact hab (by simp [ha,hb])
  · rw [hb] at hquad
    have hprod : a^2 * D = 0 := by simpa using hquad.symm
    have ha := (mul_eq_zero.mp hprod).resolve_right hp.ne'
    have ha0 : a = 0 := by simpa using ha
    exact hab (by simp [ha0,hb])

private theorem linePolynomial_isRoot {D a b t : ℤ} (p : Pell.Solution₁ D)
    (ht : a * p.x + b * p.y = t) : (linePolynomial D a b t).IsRoot p.y := by
  unfold Polynomial.IsRoot
  simp only [linePolynomial, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  rw [← ht]
  linear_combination a^2 * p.prop

/-- A Pell orbit avoids every prescribed finite set of bounded strips. -/
theorem pell_avoid (D : ℤ) (hp : 0 < D) (hn : ¬ IsSquare D)
    (S : Finset (ℤ × ℤ)) (hS : ∀ r ∈ S, r ≠ (0,0)) (B : ℕ) :
    ∃ p : Pell.Solution₁ D, ∀ r ∈ S, (B : ℤ) < |r.1*p.x + r.2*p.y| := by
  classical
  let hit := S.biUnion fun r => (Finset.Icc (-(B : ℤ)) (B : ℤ)).biUnion fun t =>
    (linePolynomial D r.1 r.2 t).roots.toFinset
  obtain ⟨e, he⟩ := Pell.IsFundamental.exists_of_not_isSquare hp hn
  have hf : ((fun n : ℤ => (e^n).y) ⁻¹' (hit : Set ℤ)).Finite :=
    hit.finite_toSet.preimage he.y_strictMono.injective.injOn
  obtain ⟨n, hn⟩ := hf.exists_notMem
  refine ⟨e^n, ?_⟩
  intro r hr
  by_contra! hbad
  apply hn
  change (e^n).y ∈ hit
  let t := r.1*(e^n).x + r.2*(e^n).y
  exact Finset.mem_biUnion.mpr ⟨r,hr, Finset.mem_biUnion.mpr ⟨t,
    Finset.mem_Icc.mpr (abs_le.mp hbad), Multiset.mem_toFinset.mpr
      ((Polynomial.mem_roots (linePolynomial_nonzero D r.1 r.2 t hp (by simpa using hS r hr))).mpr
        (linePolynomial_isRoot (e^n) rfl))⟩⟩

end Quartic324

namespace Quartic324

/-- An integer linear form in the two Pell coordinates. -/
def ev (u : ℤ × ℤ) (x y : ℤ) : ℤ := u.1*x + u.2*y

/-- Four nonzero forms, pairwise distinct even up to sign. -/
def Separated (a b r s : ℤ × ℤ) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ r ≠ 0 ∧ s ≠ 0 ∧
  a ≠ b ∧ a ≠ -b ∧ a ≠ r ∧ a ≠ -r ∧ a ≠ s ∧ a ≠ -s ∧
  b ≠ r ∧ b ≠ -r ∧ b ≠ s ∧ b ≠ -s ∧ r ≠ s ∧ r ≠ -s

private theorem ev_add (a b : ℤ × ℤ) (x y : ℤ) :
    ev (a+b) x y = ev a x y + ev b x y := by simp [ev]; ring

private theorem ev_sub (a b : ℤ × ℤ) (x y : ℤ) :
    ev (a-b) x y = ev a x y - ev b x y := by simp [ev]; ring

private theorem quartic_natAbs (c z : ℤ) : quartic c (z.natAbs : ℤ) = quartic c z := by
  rw [Int.natCast_natAbs]
  rcases le_total 0 z with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h]
    unfold quartic
    ring

/-- Sort each pair after taking its four absolute values. -/
private theorem ordered_pairs {c : ℤ} {B a b r s : ℕ}
    (ha : B < a) (hb : B < b) (hr : B < r) (hs : B < s)
    (hab : a ≠ b) (har : a ≠ r) (has' : a ≠ s)
    (hbr : b ≠ r) (hbs : b ≠ s) (hrs : r ≠ s)
    (heq : quartic c a + quartic c b = quartic c r + quartic c s) :
    ∃ a b r s : ℕ, B<a ∧ a<b ∧ B<r ∧ r<s ∧ a≠r ∧ a≠s ∧ b≠r ∧ b≠s ∧
      quartic c a + quartic c b = quartic c r + quartic c s := by
  refine ⟨min a b, max a b, min r s, max r s, ?_⟩
  rcases le_total a b with h | h <;> rcases le_total r s with k | k <;>
    simp only [min_def, max_def] <;> split_ifs <;> (repeat' constructor) <;> omega

/-- Zero avoidance for the differences handles equality; avoidance for the
sums handles equality after a change of sign. -/
theorem tail_of_pell_forms {c D : ℤ} (hd : 0 < D) (hn : ¬ IsSquare D)
    (a b r s : ℤ × ℤ) (hsep : Separated a b r s)
    (hident : ∀ p : Pell.Solution₁ D,
      quartic c (ev a p.x p.y) + quartic c (ev b p.x p.y) =
      quartic c (ev r p.x p.y) + quartic c (ev s p.x p.y)) : Tail c := by
  intro B
  let S : Finset (ℤ × ℤ) := {a,b,r,s,a-b,a+b,a-r,a+r,a-s,a+s,b-r,b+r,b-s,b+s,r-s,r+s}
  obtain ⟨ha,hb,hr,hs,hab,hab',har,har',has',has₁,hbr,hbr',hbs,hbs',hrs,hrs'⟩ := hsep
  have hS : ∀ u ∈ S, u ≠ (0,0) := by
    intro u hu heq
    subst u
    change (0 : ℤ × ℤ) ∈ S at hu
    simp only [S, Finset.mem_insert, Finset.mem_singleton, eq_comm (a := (0 : ℤ × ℤ)),
      sub_eq_zero, add_eq_zero_iff_eq_neg] at hu
    tauto
  obtain ⟨p,hp⟩ := pell_avoid D hd hn S hS B
  have hlarge (u : ℤ × ℤ) (hu : u ∈ S) : B < (ev u p.x p.y).natAbs := by
    have hx : (B : ℤ) < |ev u p.x p.y| := hp u hu
    rw [← Int.natCast_natAbs] at hx
    exact_mod_cast hx
  have hne (u v : ℤ × ℤ) (hdif : u-v ∈ S) (hadd : u+v ∈ S) :
      (ev u p.x p.y).natAbs ≠ (ev v p.x p.y).natAbs := by
    intro heq
    rcases Int.natAbs_eq_natAbs_iff.mp heq with h | h
    · have hlarge' := hlarge (u-v) hdif
      rw [ev_sub, h, sub_self] at hlarge'
      simp at hlarge'
    · have hlarge' := hlarge (u+v) hadd
      rw [ev_add, h, neg_add_cancel] at hlarge'
      simp at hlarge'
  apply ordered_pairs (hlarge a (by simp [S])) (hlarge b (by simp [S]))
    (hlarge r (by simp [S])) (hlarge s (by simp [S]))
    (hne a b (by simp [S]) (by simp [S])) (hne a r (by simp [S]) (by simp [S]))
    (hne a s (by simp [S]) (by simp [S])) (hne b r (by simp [S]) (by simp [S]))
    (hne b s (by simp [S]) (by simp [S])) (hne r s (by simp [S]) (by simp [S]))
  simpa only [quartic_natAbs] using hident p


end Quartic324

namespace Quartic324

private theorem between_squares {d n : ℤ} (hn : 0 ≤ n)
    (h₁ : n ^ 2 < d) (h₂ : d < (n + 1) ^ 2) : 0 < d ∧ ¬ IsSquare d := by
  refine ⟨lt_of_le_of_lt (sq_nonneg n) h₁, ?_⟩
  rintro ⟨k, hk⟩
  by_cases h : |k| ≤ n
  · have hs := (sq_le_sq₀ (abs_nonneg k) hn).2 h
    rw [sq_abs] at hs
    nlinarith only [hk, hs, h₁]
  · have hh : n + 1 ≤ |k| := by omega
    have hs := (sq_le_sq₀ (by omega : 0 ≤ n + 1) (abs_nonneg k)).2 hh
    rw [sq_abs] at hs
    nlinarith only [hk, hs, h₂]

private theorem exterior (c : ℤ) (hc : c ≤ -291 ∨ 260 ≤ c) :
    0 < disc c ∧ ¬ IsSquare (disc c) := by
  have bounds : 0 ≤ c^2 + 15*c + 13 ∧ 0 < c^2 + 290*c - 169 ∧ 0 < c^2 - 260*c + 196 := by
    rcases hc with h | h
    · have hmul := mul_nonneg (by omega : 0 ≤ -c-291) (by omega : 0 ≤ -c+1)
      exact ⟨by nlinarith [sq_nonneg c], by nlinarith, by nlinarith [sq_nonneg c]⟩
    · have hmul := mul_nonneg (by omega : 0 ≤ c) (by omega : 0 ≤ c-260)
      exact ⟨by nlinarith [sq_nonneg c], by nlinarith [sq_nonneg c], by nlinarith⟩
  apply between_squares bounds.1 <;> unfold disc
  · nlinarith only [bounds.2.1]
  · nlinarith only [bounds.2.2]

set_option maxRecDepth 20000 in
private theorem negative_cases : ∀ i : Fin 272,
    0 < disc ((i.val : ℤ) - 290) ∧ ¬ IsSquare (disc ((i.val : ℤ) - 290)) := by
  decide +kernel

set_option maxRecDepth 20000 in
private theorem positive_cases : ∀ i : Fin 259,
    0 < disc ((i.val : ℤ) + 1) ∧ ¬ IsSquare (disc ((i.val : ℤ) + 1)) := by
  decide +kernel

theorem disc_good (c : ℤ) (hc : c ≤ -19 ∨ 1 ≤ c) : 0 < disc c ∧ ¬ IsSquare (disc c) := by
  by_cases he : c ≤ -291 ∨ 260 ≤ c
  · exact exterior c he
  rcases hc with h | h
  · let i : Fin 272 := ⟨(c + 290).toNat, by omega⟩
    have hi : (i.val : ℤ) - 290 = c := by dsimp [i]; omega
    simpa only [hi] using negative_cases i
  · let i : Fin 259 := ⟨(c - 1).toNat, by omega⟩
    have hi : (i.val : ℤ) + 1 = c := by dsimp [i]; omega
    simpa only [hi] using positive_cases i


end Quartic324

namespace Quartic324

/-- A difference of two quartic differences factors through the norm-one conic. -/
theorem tangent_factor (c v w : ℤ) :
    quartic c (v + 2*(c+8)*c*w) + quartic c (2*v - (c+2)*c*w) -
      (quartic c (-v + 2*(c+8)*c*w) + quartic c (2*v + (c+2)*c*w)) =
      -48*c^2*v*w * (v^2 - disc c*w^2 - 1) := by
  unfold quartic disc
  ring

theorem tangent_on_unit (c : ℤ) (p : Pell.Solution₁ (disc c)) :
    quartic c (p.x + 2*(c+8)*c*p.y) + quartic c (2*p.x - (c+2)*c*p.y) =
    quartic c (-p.x + 2*(c+8)*c*p.y) + quartic c (2*p.x + (c+2)*c*p.y) := by
  apply sub_eq_zero.mp
  rw [tangent_factor, p.prop]
  ring

end Quartic324

namespace Quartic324

/-- For this range, the tangent construction supplies four separated integral linear forms. -/
theorem generic_tail (c : ℤ) (hc : c ≤ -19 ∨ 1 ≤ c) : Tail c := by
  obtain ⟨hd, hn⟩ := disc_good c hc
  have hc0 : c ≠ 0 := by omega
  have h8 : c + 8 ≠ 0 := by omega
  have h2 : c + 2 ≠ 0 := by omega
  have hX : 2 * (c+8) * c ≠ 0 := mul_ne_zero (mul_ne_zero (by decide) h8) hc0
  have hK : (c+2)*c ≠ 0 := mul_ne_zero h2 hc0
  apply tail_of_pell_forms hd hn
    (1, 2*(c+8)*c) (2, -((c+2)*c)) (-1, 2*(c+8)*c) (2, (c+2)*c)
  · norm_num [Separated, Prod.ext_iff, Prod.fst_neg, Prod.snd_neg]
    omega
  · intro p
    simpa only [ev, one_mul, neg_one_mul, neg_mul, sub_eq_add_neg] using tangent_on_unit c p

end Quartic324

namespace Quartic324

/-- Numeric certificate: the difference of the two quartic sums is a multiple
of the Pell equation. The signed coefficient of the multiple is forced by the
degree-two part of the two sums. -/
private theorem certified_tail (c D : ℤ) (a b r s : ℤ × ℤ)
    (hd : 0 < D) (hn : ¬ IsSquare D)
    (hsep : Separated a b r s)
    (hid : ∀ x y : ℤ,
      quartic c (ev a x y) + quartic c (ev b x y) =
      quartic c (ev r x y) + quartic c (ev s x y) +
        (-c) * ((ev a x y)^2 + (ev b x y)^2 - (ev r x y)^2 - (ev s x y)^2) *
        (x^2 - D*y^2 - 1)) : Tail c := by
  apply tail_of_pell_forms hd hn a b r s hsep
  intro p
  simpa only [p.prop, sub_self, mul_zero, add_zero] using hid p.x p.y

/-- The eighteen exceptional negative coefficients have nondegenerate Pell
families obtained by deforming explicit positive collisions. -/
theorem exceptional_tail (c : ℤ) (hc1 : -18 ≤ c) (hc2 : c ≤ -1) : Tail c := by
  interval_cases c
  all_goals first
    | apply certified_tail (-18) 26892 (3, 432) (42, 6966) (30, 4914) (39, 6480)
    | apply certified_tail (-17) 4392060 (9, 18490) (13, 27656) (11, 22750) (12, 25594)
    | apply certified_tail (-16) 1010884 (8, 7792) (9, 10050) (3, 2262) (10, 10964)
    | apply certified_tail (-15) 13319912844 (6, 680382) (132, 15250374) (93, 10732536) (123, 14212836)
    | apply certified_tail (-14) 14363316 (10, 37200) (33, 125910) (25, 94470) (30, 114624)
    | apply certified_tail (-13) 104529500 (27, 275164) (59, 604724) (34, 346914) (58, 594526)
    | apply certified_tail (-12) 39861412 (9, 55386) (34, 217052) (20, 125632) (33, 210810)
    | apply certified_tail (-11) 28930484196 (11, 1853742) (65, 11076618) (49, 8330538) (59, 10058190)
    | apply certified_tail (-10) 856760816 (11, 317956) (33, 971368) (23, 671308) (31, 913176)
    | apply certified_tail (-9) 14607428 (9, 33918) (42, 161148) (30, 114516) (39, 149730)
    | apply certified_tail (-8) 26892 (2, 288) (28, 4644) (20, 3276) (26, 4320)
    | apply certified_tail (-7) 349232 (4, 2252) (21, 12544) (16, 9428) (19, 11376)
    | apply certified_tail (-6) 819024 (17, 15348) (45, 40764) (37, 33468) (39, 35340)
    | apply certified_tail (-5) 262044 (4, 1958) (12, 6254) (9, 4568) (11, 5752)
    | apply certified_tail (-4) 14607428 (6, 22612) (28, 107432) (20, 76344) (26, 99820)
    | apply certified_tail (-3) 524172 (4, 2850) (30, 21774) (23, 16644) (27, 19608)
    | apply certified_tail (-2) 26892 (1, 144) (14, 2322) (10, 1638) (13, 2160)
    | apply certified_tail (-1) 14607428 (3, 11306) (14, 53716) (10, 38172) (13, 49910)
  all_goals first
    | decide +kernel
    | unfold Separated; decide
    | intro x y; simp only [quartic, ev]; ring

/-- Euler's collision remains a collision after every common dilation. -/
theorem zero_tail : Tail 0 := by
  intro B
  let k := B + 1
  refine ⟨59*k, 158*k, 133*k, 134*k, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | dsimp [k]; omega
    | push_cast; simp only [quartic]; ring


end Quartic324

open Quartic324

/-- Every integer quadratic perturbation of the fourth powers has a repeated pair sum
at four distinct positive indices above any prescribed bound. -/
theorem solution (c : ℤ) (N : ℕ) :
    ∃ a b r s : ℕ, N < a ∧ a < b ∧ N < r ∧ r < s ∧
      a ≠ r ∧ a ≠ s ∧ b ≠ r ∧ b ≠ s ∧
      (a : ℤ)^4 + c*(a : ℤ)^2 + ((b : ℤ)^4 + c*(b : ℤ)^2) =
      (r : ℤ)^4 + c*(r : ℤ)^2 + ((s : ℤ)^4 + c*(s : ℤ)^2) := by
  change ∃ a b r s : ℕ, N < a ∧ a < b ∧ N < r ∧ r < s ∧
    a ≠ r ∧ a ≠ s ∧ b ≠ r ∧ b ≠ s ∧
    quartic c a + quartic c b = quartic c r + quartic c s
  by_cases h : c ≤ -19 ∨ 1 ≤ c
  · exact generic_tail c h N
  by_cases hz : c = 0
  · subst c
    exact zero_tail N
  exact exceptional_tail c (by omega) (by omega) N
