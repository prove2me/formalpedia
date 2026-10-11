-- Prove2me | solution 1 for BookProof.SmBrstGhost.brstCharge_nilpotent
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:55:50.664698+00:00
-- url     : https://prove2.me/submissions/219eb091-c872-4f59-98ea-990ce287921c

-- Generated from ChapterSmBrstGhost.lean — solution of BookProof.SmBrstGhost.brstCharge_nilpotent
import Mathlib
import Definitions.Def_ChapterSmBrstGhost
import Theorems.Thm_BookProof_SmBrstGhost_sum_rotate3
import Theorems.Thm_BookProof_SmBrstGhost_sum_rotate4
import Theorems.Thm_BookProof_BRSTNilpotent_brst_charge_nilpotent
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterYangMillsSU3
import Definitions.Def_ChapterBRSTNilpotent
open BookProof.SmBrstGhost




open BookProof.SmCar BookProof.BRSTNilpotent BookProof.YangMillsSU3

noncomputable section

variable {m : ℕ}
variable {R : Type*} [Ring R] [Algebra ℝ R] {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (f : Fin n → Fin n → Fin n → ℝ) (χ β G : Fin n → R)
    (hCAR : GhostCAR χ β)
    (hGχ : ∀ a b, G a * χ b = χ b * G a) (hGβ : ∀ a b, G a * β b = β b * G a)
    (hclose : ∀ a b, G a * G b - G b * G a = ∑ c, f a b c • G c)
    (hf12 : ∀ a b c, f a b c = -f b a c)
    (hjac : ∀ a b c h : Fin n,
      ∑ e, (f a b e * f e c h + f b c e * f e a h + f c a e * f e b h) = 0) :
    brstCharge f χ β G * brstCharge f χ β G = 0 := by

  classical
  -- the two halves of the charge
  set X : R := ∑ a, χ a * G a with hXdef
  -- moving a ghost creation operator through a cubic ghost monomial
  have hmove : ∀ a d g h : Fin n,
      χ a * (χ d * χ g * β h) + (χ d * χ g * β h) * χ a
        = (if h = a then (1 : R) else 0) * (χ d * χ g) := by
    intro a d g h
    have hb : β h * χ a = (if h = a then (1 : R) else 0) - χ a * β h :=
      eq_sub_of_add_eq (hCAR.betachi h a)
    have hda : χ d * χ a = -(χ a * χ d) := eq_neg_of_add_eq_zero_left (hCAR.chichi d a)
    have hga : χ g * χ a = -(χ a * χ g) := eq_neg_of_add_eq_zero_left (hCAR.chichi g a)
    have h3 : χ d * χ g * χ a = χ a * (χ d * χ g) := by
      calc χ d * χ g * χ a = χ d * (χ g * χ a) := by noncomm_ring
        _ = χ d * -(χ a * χ g) := by rw [hga]
        _ = -((χ d * χ a) * χ g) := by noncomm_ring
        _ = -((-(χ a * χ d)) * χ g) := by rw [hda]
        _ = χ a * (χ d * χ g) := by noncomm_ring
    have key : (χ d * χ g * β h) * χ a
        = (if h = a then (1 : R) else 0) * (χ d * χ g) - χ a * (χ d * χ g * β h) := by
      have h1 : (χ d * χ g * β h) * χ a = χ d * χ g * (β h * χ a) := by noncomm_ring
      rw [h1, hb]
      have h2 : χ d * χ g * ((if h = a then (1 : R) else 0) - χ a * β h)
          = (if h = a then (1 : R) else 0) * (χ d * χ g) - (χ d * χ g * χ a) * β h := by
        by_cases hh : h = a
        · simp only [hh, if_pos]; noncomm_ring
        · simp only [if_neg hh]; noncomm_ring
      rw [h2, h3]
      noncomm_ring
    rw [key]
    abel
  -- the square of the linear part
  have hXXexp : X * X = ∑ a, ∑ b, (χ a * χ b) * (G a * G b) := by
    rw [hXdef, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [show (χ a * G a) * (χ b * G b) = χ a * (G a * χ b) * G b by noncomm_ring, hGχ a b]
    noncomm_ring
  have hswap : (∑ a, ∑ b, (χ a * χ b) * (G b * G a))
      = -∑ a, ∑ b, (χ a * χ b) * (G a * G b) := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [show χ b * χ a = -(χ a * χ b) from eq_neg_of_add_eq_zero_left (hCAR.chichi b a)]
    noncomm_ring
  have hXX2 : (2 : ℝ) • (X * X) = ∑ a, ∑ b, ∑ c, f a b c • (χ a * χ b * G c) := by
    rw [two_smul, hXXexp]
    nth_rewrite 2 [show (∑ a, ∑ b, (χ a * χ b) * (G a * G b))
        = -∑ a, ∑ b, (χ a * χ b) * (G b * G a) from by rw [hswap, neg_neg]]
    rw [← sub_eq_add_neg, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← mul_sub, hclose a b, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by rw [mul_smul_comm]
  -- the cross term
  have hXQ : X * Q f χ β + Q f χ β * X = ∑ a, ∑ b, ∑ c, f a b c • (χ a * χ b * G c) := by
    have hX1 : X * Q f χ β
        = ∑ a, ∑ d, ∑ g, ∑ h, f d g h • ((χ a * G a) * (χ d * χ g * β h)) := by
      rw [hXdef, Q, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun h _ => by rw [mul_smul_comm]
    have hQ1 : Q f χ β * X
        = ∑ a, ∑ d, ∑ g, ∑ h, f d g h • ((χ d * χ g * β h) * (χ a * G a)) := by
      rw [← sum_rotate4 (fun a d g h => f d g h • ((χ d * χ g * β h) * (χ a * G a)))]
      rw [hXdef, Q, Finset.sum_mul]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [smul_mul_assoc, Finset.mul_sum, Finset.smul_sum]
    rw [hX1, hQ1, ← Finset.sum_add_distrib]
    have hcollapse : ∀ a : Fin n,
        ((∑ d, ∑ g, ∑ h, f d g h • ((χ a * G a) * (χ d * χ g * β h)))
          + ∑ d, ∑ g, ∑ h, f d g h • ((χ d * χ g * β h) * (χ a * G a)))
        = ∑ d, ∑ g, f d g a • (χ d * χ g * G a) := by
      intro a
      simp only [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun d _ => ?_
      refine Finset.sum_congr rfl fun g _ => ?_
      have hterm : ∀ h : Fin n,
          f d g h • ((χ a * G a) * (χ d * χ g * β h))
            + f d g h • ((χ d * χ g * β h) * (χ a * G a))
          = f d g h • ((if h = a then (1 : R) else 0) * (χ d * χ g * G a)) := by
        intro h
        rw [← smul_add]
        congr 1
        have hc1 : (χ a * G a) * (χ d * χ g * β h) = (χ a * (χ d * χ g * β h)) * G a := by
          have hg1 : G a * (χ d * χ g * β h) = (χ d * χ g * β h) * G a := by
            rw [show G a * (χ d * χ g * β h) = ((G a * χ d) * χ g) * β h by noncomm_ring,
              hGχ a d,
              show ((χ d * G a) * χ g) * β h = (χ d * (G a * χ g)) * β h by noncomm_ring,
              hGχ a g,
              show (χ d * (χ g * G a)) * β h = (χ d * χ g) * (G a * β h) by noncomm_ring,
              hGβ a h]
            noncomm_ring
          calc (χ a * G a) * (χ d * χ g * β h)
              = χ a * (G a * (χ d * χ g * β h)) := by noncomm_ring
            _ = χ a * ((χ d * χ g * β h) * G a) := by rw [hg1]
            _ = (χ a * (χ d * χ g * β h)) * G a := by noncomm_ring
        have hc2 : (χ d * χ g * β h) * (χ a * G a)
            = ((χ d * χ g * β h) * χ a) * G a := by noncomm_ring
        rw [hc1, hc2, ← add_mul, hmove a d g h]
        noncomm_ring
      rw [Finset.sum_congr rfl fun h (_ : h ∈ Finset.univ) => hterm h]
      rw [Finset.sum_eq_single a]
      · rw [if_pos rfl, one_mul]
      · intro h _ hh
        rw [if_neg hh, zero_mul, smul_zero]
      · intro ha
        exact absurd (Finset.mem_univ a) ha
    rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => hcollapse a]
    rw [← sum_rotate3 (fun a d g => f d g a • (χ d * χ g * G a))]
  -- nilpotency of the cubic ghost term
  have hQnil : Q f χ β * Q f χ β = 0 := brst_charge_nilpotent f χ β hCAR hf12 hjac
  -- assemble
  have h2 : (2 : ℝ) • (brstCharge f χ β G * brstCharge f χ β G) = 0 := by
    have hexp : brstCharge f χ β G * brstCharge f χ β G
        = X * X - (1 / 2 : ℝ) • (X * Q f χ β + Q f χ β * X)
          + (1 / 2 : ℝ) • ((1 / 2 : ℝ) • (Q f χ β * Q f χ β)) := by
      rw [brstCharge, ← hXdef]
      simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub]
      abel
    have htwo : ((2 : ℝ) * (1 / 2 : ℝ)) = 1 := by norm_num
    rw [hexp, hQnil, smul_zero, smul_zero, add_zero, smul_sub, smul_smul, htwo, one_smul,
      hXX2, hXQ, sub_self]
  have hne : (2 : ℝ) ≠ 0 := two_ne_zero
  rcases smul_eq_zero.mp h2 with h | h
  · exact absurd h hne
  · exact h
