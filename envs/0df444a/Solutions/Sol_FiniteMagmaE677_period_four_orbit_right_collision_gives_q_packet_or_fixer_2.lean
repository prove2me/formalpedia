-- Prove2me | solution 2 for FiniteMagmaE677.period_four_orbit_right_collision_gives_q_packet_or_fixer
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T01:40:46.71243+00:00
-- url     : https://prove2.me/submissions/e937a8d5-0436-465a-9741-4daedcac615d

import Definitions.Def_FiniteMagmaE677
import Mathlib.Tactic

/-!
Port of the proved period-four orbit-right-collision dispatcher
(`e677_minimalPeriodFour_orbitRightCollision_distinguishedPacket_or_hasFixer`)
to a self-contained file.  All helpers are private and stated over a private
magma class; `solution` instantiates the class with `op`.
-/

universe u

private class PMagma (α : Type u) where
  op : α → α → α

local infix:65 " ◇ " => PMagma.op

private abbrev PE677 (α : Type u) [PMagma α] : Prop :=
  ∀ x y : α, x = y ◇ (x ◇ ((y ◇ x) ◇ y))

section Port

variable {α : Type u} [PMagma α]

private def PHasFixerAt (x : α) : Prop :=
  ∃ y : α, y ◇ x = x

private theorem p_leftMul_surj (h : PE677 α) (y : α) :
    Function.Surjective (fun x => y ◇ x) := by
  intro x
  exact ⟨x ◇ ((y ◇ x) ◇ y), (h x y).symm⟩

private theorem p_left_cancel [Finite α] (h : PE677 α) (y : α) {a b : α}
    (hab : y ◇ a = y ◇ b) : a = b :=
  ((Finite.surjective_iff_bijective).mp (p_leftMul_surj h y)).1 hab

private def orbitPoint (x : α) (k : ℕ) : α :=
  (fun z => x ◇ z)^[k] x

private def orbitQ (x : α) (i j : ℕ) : α :=
  orbitPoint x j ◇ ((orbitPoint x i ◇ orbitPoint x j) ◇ orbitPoint x i)

private def PMinimalOrbitPeriod (x : α) (d : ℕ) : Prop :=
  0 < d ∧
    (fun z => x ◇ z)^[d] x = x ∧
      ∀ e : ℕ, 0 < e → (fun z => x ◇ z)^[e] x = x → d ≤ e

private theorem orbitQ_spec_bare (h : PE677 α) (x : α) (i j : ℕ) :
    orbitPoint x i ◇ orbitQ x i j = orbitPoint x j := by
  unfold orbitQ
  exact (h (orbitPoint x j) (orbitPoint x i)).symm

private theorem q_packet_ne_c3 [Finite α]
    (h : PE677 α)
    (x c1 c2 c3 q : α)
    (hc1 : x ◇ x = c1)
    (hc2 : x ◇ c1 = c2)
    (hc3 : x ◇ c2 = c3)
    (hcycle : x ◇ c3 = x)
    (hq : c2 ◇ x = q)
    (hpacket1 : c1 ◇ q = x)
    (hpacket2 : c2 ◇ q = c1)
    (hne : c2 ≠ c3) :
    q ≠ c3 := by
  intro hqeq
  have h20 : c2 ◇ x = c3 := hq.trans hqeq
  have h13 : c1 ◇ c3 = x := by
    rw [← hqeq]
    exact hpacket1
  have h23 : c2 ◇ c3 = c1 := by
    rw [← hqeq]
    exact hpacket2
  have h1a : x ◇ (x ◇ (c1 ◇ x)) = x := by
    simpa only [hc1] using (h x x).symm
  have h1 : x ◇ (c1 ◇ x) = c3 :=
    p_left_cancel h x (h1a.trans hcycle.symm)
  have h3 : c1 ◇ x = c2 :=
    p_left_cancel h x (h1.trans hc3.symm)
  have h4 : c1 ◇ (x ◇ (c2 ◇ c1)) = x := by
    simpa only [h3] using (h x c1).symm
  have h5 : x ◇ (c2 ◇ c1) = c3 :=
    p_left_cancel h c1 (h4.trans h13.symm)
  have h6 : c2 ◇ c1 = c2 :=
    p_left_cancel h x (h5.trans hc3.symm)
  have h7 : c2 ◇ (c1 ◇ (c2 ◇ c2)) = c1 := by
    simpa only [h6] using (h c1 c2).symm
  have h8 : c1 ◇ (c2 ◇ c2) = c3 :=
    p_left_cancel h c2 (h7.trans h23.symm)
  have h9 : c2 ◇ c2 = c1 ◇ ((c2 ◇ c2) ◇ (c3 ◇ c1)) := by
    simpa only [h8] using h (c2 ◇ c2) c1
  have h10a : x ◇ (c3 ◇ c1) = c3 := by
    simpa only [hcycle, hc1] using (h c3 x).symm
  have h10 : c2 = c3 ◇ c1 :=
    p_left_cancel h x (hc3.trans h10a.symm)
  have h11 : c2 ◇ c2 = c1 ◇ ((c2 ◇ c2) ◇ c2) := by
    simpa only [h10] using h9
  have h12a : c1 ◇ (c3 ◇ c2) = c3 := by
    simpa only [h13, hc2] using (h c3 c1).symm
  have h12 : c3 ◇ c2 = c2 ◇ c2 :=
    p_left_cancel h c1 (h12a.trans h8.symm)
  have h13' : c3 ◇ c2 = c1 ◇ ((c3 ◇ c2) ◇ c2) := by
    simpa only [h12] using h11
  have h14 : c2 ◇ (c2 ◇ ((c3 ◇ c2) ◇ c2)) = c2 := by
    simpa only [h12] using (h c2 c2).symm
  have h15 : c1 = c2 ◇ ((c3 ◇ c2) ◇ c2) :=
    p_left_cancel h c2 (h6.trans h14.symm)
  have h16 : c3 = (c3 ◇ c2) ◇ c2 :=
    p_left_cancel h c2 (h23.trans h15)
  have h17 : c3 ◇ c2 = x := by
    calc
      c3 ◇ c2 = c1 ◇ ((c3 ◇ c2) ◇ c2) := h13'
      _ = c1 ◇ c3 := by rw [← h16]
      _ = x := h13
  have h18 : c2 ◇ (x ◇ (c3 ◇ c2)) = x := by
    simpa only [h20] using (h x c2).symm
  have h20' : x ◇ (c3 ◇ c2) = c2 := by
    apply p_left_cancel h c2
    calc
      c2 ◇ (x ◇ (c3 ◇ c2)) = x := h18
      _ = c3 ◇ c2 := h17.symm
      _ = c2 ◇ c2 := h12
  have h21 : c1 = c3 ◇ c2 :=
    p_left_cancel h x (hc2.trans h20'.symm)
  apply hne
  apply p_left_cancel h c2
  calc
    c2 ◇ c2 = c3 ◇ c2 := h12.symm
    _ = c1 := h21.symm
    _ = c2 ◇ c3 := h23.symm

private theorem backward_recurrence [Finite α] (h : PE677 α) (a b : α) :
    a = (b ◇ a) ◇ ((b ◇ (b ◇ a)) ◇ b) := by
  apply p_left_cancel h b
  exact h (b ◇ a) b

private theorem orbitPoint_recurrence [Finite α] (h : PE677 α) (x : α) (k : ℕ) :
    orbitPoint x k = orbitPoint x (k + 1) ◇ (orbitPoint x (k + 2) ◇ x) := by
  unfold orbitPoint
  simp only [Function.iterate_succ', Function.comp]
  exact backward_recurrence h ((fun z ↦ x ◇ z)^[k] x) x

private theorem orbitQ_subdiag_eq_rightMul [Finite α]
    (h : PE677 α) (x : α) (k : ℕ) :
    orbitQ x (k + 1) k = orbitPoint x (k + 2) ◇ x := by
  apply p_left_cancel h (orbitPoint x (k + 1))
  calc
    orbitPoint x (k + 1) ◇ orbitQ x (k + 1) k = orbitPoint x k :=
      orbitQ_spec_bare h x (k + 1) k
    _ = orbitPoint x (k + 1) ◇ (orbitPoint x (k + 2) ◇ x) :=
      orbitPoint_recurrence h x k

private theorem d4_q_ne_x_c1_c2 [Finite α]
    (h : PE677 α) {x c1 c2 : α}
    (hc2 : x ◇ c1 = c2)
    (hpacket2 : c2 ◇ (c2 ◇ x) = c1)
    (hx_ne_c1 : x ≠ c1) :
    c2 ◇ x ≠ x ∧ c2 ◇ x ≠ c1 ∧ c2 ◇ x ≠ c2 := by
  constructor
  · intro hqx
    apply hx_ne_c1
    calc
      x = c2 ◇ x := hqx.symm
      _ = c2 ◇ (c2 ◇ x) := congrArg (fun z => c2 ◇ z) hqx.symm
      _ = c1 := hpacket2
  constructor
  · intro hqc1
    apply hx_ne_c1
    apply p_left_cancel h c2
    calc
      c2 ◇ x = c1 := hqc1
      _ = c2 ◇ (c2 ◇ x) := hpacket2.symm
      _ = c2 ◇ c1 := congrArg (fun z => c2 ◇ z) hqc1
  · intro hqc2
    apply hx_ne_c1
    have hc2c2 : c2 ◇ c2 = c1 := by
      simpa only [hqc2] using hpacket2
    calc
      x = c2 ◇ (x ◇ ((c2 ◇ x) ◇ c2)) := h x c2
      _ = c2 ◇ (x ◇ (c2 ◇ c2)) := by rw [hqc2]
      _ = c2 ◇ (x ◇ c1) := by rw [hc2c2]
      _ = c2 ◇ c2 := by rw [hc2]
      _ = c1 := hc2c2

private theorem d4_q_source_return [Finite α]
    (h : PE677 α) {x c1 c2 : α}
    (hpacket2 : c2 ◇ (c2 ◇ x) = c1) :
    x = (c2 ◇ x) ◇ (c1 ◇ c2) := by
  apply p_left_cancel h c2
  calc
    c2 ◇ x = c2 ◇ ((c2 ◇ x) ◇ ((c2 ◇ (c2 ◇ x)) ◇ c2)) :=
      h (c2 ◇ x) c2
    _ = c2 ◇ ((c2 ◇ x) ◇ (c1 ◇ c2)) := by rw [hpacket2]

private theorem d4_q_r_partial_freshness [Finite α]
    (h : PE677 α) {x c1 c2 c3 : α}
    (hc1 : x ◇ x = c1)
    (hc2 : x ◇ c1 = c2)
    (hcollision : c2 ◇ x = c3 ◇ x)
    (hpacket1 : c1 ◇ (c2 ◇ x) = x)
    (hpacket2 : c2 ◇ (c2 ◇ x) = c1)
    (hx_ne_c1 : x ≠ c1)
    (hx_ne_c2 : x ≠ c2)
    (hc1_ne_c2 : c1 ≠ c2) :
    c1 ◇ c2 ≠ x ∧
      c1 ◇ c2 ≠ c2 ∧
      c1 ◇ c2 ≠ c3 ∧
      c1 ◇ c2 ≠ c2 ◇ x := by
  have hqfresh := d4_q_ne_x_c1_c2 h hc2 hpacket2 hx_ne_c1
  have hxqr := d4_q_source_return h hpacket2
  constructor
  · intro hrx
    exact hqfresh.2.2 <| p_left_cancel h c1 <| by
      calc
        c1 ◇ (c2 ◇ x) = x := hpacket1
        _ = c1 ◇ c2 := hrx.symm
  constructor
  · intro hrc2
    have hqc2 : (c2 ◇ x) ◇ c2 = x := by
      calc
        (c2 ◇ x) ◇ c2 = (c2 ◇ x) ◇ (c1 ◇ c2) :=
          congrArg (fun z => (c2 ◇ x) ◇ z) hrc2.symm
        _ = x := hxqr.symm
    have hx_c2c1 : x = c2 ◇ c1 := by
      calc
        x = c2 ◇ (x ◇ ((c2 ◇ x) ◇ c2)) := h x c2
        _ = c2 ◇ (x ◇ x) := by rw [hqc2]
        _ = c2 ◇ c1 := by rw [hc1]
    apply hx_ne_c2
    symm
    calc
      c2 = c1 ◇ (c2 ◇ ((c1 ◇ c2) ◇ c1)) := h c2 c1
      _ = c1 ◇ (c2 ◇ (c2 ◇ c1)) := by rw [hrc2]
      _ = c1 ◇ (c2 ◇ x) := by rw [← hx_c2c1]
      _ = x := hpacket1
  constructor
  · intro hrc3
    have hqc3 : (c2 ◇ x) ◇ c3 = x := by
      calc
        (c2 ◇ x) ◇ c3 = (c2 ◇ x) ◇ (c1 ◇ c2) :=
          congrArg (fun z => (c2 ◇ x) ◇ z) hrc3.symm
        _ = x := hxqr.symm
    have hx_c3c1 : x = c3 ◇ c1 := by
      calc
        x = c3 ◇ (x ◇ ((c3 ◇ x) ◇ c3)) := h x c3
        _ = c3 ◇ (x ◇ ((c2 ◇ x) ◇ c3)) := by rw [hcollision]
        _ = c3 ◇ (x ◇ x) := by rw [hqc3]
        _ = c3 ◇ c1 := by rw [hc1]
    apply hx_ne_c2
    symm
    calc
      c2 = c1 ◇ (c2 ◇ ((c1 ◇ c2) ◇ c1)) := h c2 c1
      _ = c1 ◇ (c2 ◇ (c3 ◇ c1)) := by rw [hrc3]
      _ = c1 ◇ (c2 ◇ x) := by rw [← hx_c3c1]
      _ = x := hpacket1
  · intro hr
    have h45 : x = c1 ◇ (c1 ◇ c2) := by
      calc
        x = c1 ◇ (c2 ◇ x) := hpacket1.symm
        _ = c1 ◇ (c1 ◇ c2) := by rw [← hr]
    have h46 : c1 = c2 ◇ (c1 ◇ c2) := by
      calc
        c1 = c2 ◇ (c2 ◇ x) := hpacket2.symm
        _ = c2 ◇ (c1 ◇ c2) := by rw [← hr]
    have h62 : ∀ z : α, c1 ◇ c2 = c1 ◇ z → c2 = z := by
      intro z hz
      exact p_left_cancel h c1 hz
    have h67 : ∀ z : α, c1 = c2 ◇ z → c1 ◇ c2 = z := by
      intro z hz
      apply p_left_cancel h c2
      exact h46.symm.trans hz
    have h212 : c2 = (c1 ◇ c2) ◇ ((c1 ◇ (c1 ◇ c2)) ◇ c1) := by
      apply h62
      simpa using h (c1 ◇ c2) c1
    have h213 : c2 = (c1 ◇ c2) ◇ (x ◇ c1) := by
      simpa [h45] using h212
    have h214 : c2 = (c1 ◇ c2) ◇ c2 := by
      simpa [hc2] using h213
    have h216 : c2 = (c1 ◇ c2) ◇ (c2 ◇ (c2 ◇ (c1 ◇ c2))) := by
      calc
        c2 = (c1 ◇ c2) ◇ (c2 ◇ (((c1 ◇ c2) ◇ c2) ◇ (c1 ◇ c2))) :=
          h c2 (c1 ◇ c2)
        _ = (c1 ◇ c2) ◇ (c2 ◇ (c2 ◇ (c1 ◇ c2))) := by rw [← h214]
    have h218 : ∀ z : α, c2 = (c1 ◇ c2) ◇ z → c2 = z := by
      intro z hz
      apply p_left_cancel h (c1 ◇ c2)
      exact h214.symm.trans hz
    have h219 : c2 = (c1 ◇ c2) ◇ (c2 ◇ c1) := by
      calc
        c2 = (c1 ◇ c2) ◇ (c2 ◇ (c2 ◇ (c1 ◇ c2))) := h216
        _ = (c1 ◇ c2) ◇ (c2 ◇ c1) := by rw [← h46]
    have h229 : c2 = c2 ◇ c1 := h218 _ h219
    have h234 : c1 = c2 ◇ (c1 ◇ (c2 ◇ c2)) := by
      calc
        c1 = c2 ◇ (c1 ◇ (((c2 ◇ c1) ◇ c2))) := h c1 c2
        _ = c2 ◇ (c1 ◇ (c2 ◇ c2)) := by rw [← h229]
    have h236 : ∀ z : α, c2 = c2 ◇ z → c1 = z := by
      intro z hz
      apply p_left_cancel h c2
      exact h229.symm.trans hz
    have h249 : c1 ◇ c2 = c1 ◇ (c2 ◇ c2) := h67 _ h234
    have h258 : c2 = c2 ◇ c2 := h62 _ h249
    exact hc1_ne_c2 (h236 _ h258)

private theorem d4_q_s_partial_freshness [Finite α]
    (h : PE677 α) {x c1 c2 c3 : α}
    (hc1 : x ◇ x = c1)
    (hc3 : x ◇ c2 = c3)
    (hcycle : x ◇ c3 = x)
    (hcollision : c2 ◇ x = c3 ◇ x)
    (hpacket2 : c2 ◇ (c2 ◇ x) = c1)
    (hx_ne_c1 : x ≠ c1)
    (hx_ne_c2 : x ≠ c2)
    (hc2_ne_c3 : c2 ≠ c3) :
    c3 ◇ (c2 ◇ x) ≠ x ∧
      c3 ◇ (c2 ◇ x) ≠ c1 ∧
      c3 ◇ (c2 ◇ x) ≠ c2 ∧
      c3 ◇ (c2 ◇ x) ≠ c2 ◇ x := by
  constructor
  · intro hs
    have h146 : c2 ◇ x = c3 ◇ ((c2 ◇ x) ◇ x) := by
      simpa only [hs, hcycle] using h (c2 ◇ x) c3
    have hx_eq_qx : x = (c2 ◇ x) ◇ x := by
      apply p_left_cancel h c3
      calc
        c3 ◇ x = c2 ◇ x := hcollision.symm
        _ = c3 ◇ ((c2 ◇ x) ◇ x) := h146
    have h174 : x = (c2 ◇ x) ◇ (x ◇ (x ◇ (c2 ◇ x))) := by
      simpa only [← hx_eq_qx] using h x (c2 ◇ x)
    have h188 : x = x ◇ (x ◇ (c2 ◇ x)) := by
      apply p_left_cancel h (c2 ◇ x)
      exact hx_eq_qx.symm.trans h174
    have hc3_eq_xq : c3 = x ◇ (c2 ◇ x) := by
      apply p_left_cancel h x
      exact hcycle.trans h188
    have hc2_eq_q : c2 = c2 ◇ x := by
      apply p_left_cancel h x
      exact hc3.trans hc3_eq_xq
    have hc2_eq_s : c2 = c3 ◇ (c2 ◇ x) := by
      have hq_x : (c2 ◇ x) ◇ x = c2 ◇ x :=
        congrArg (fun z : α => z ◇ x) hc2_eq_q.symm
      calc
        c2 = c2 ◇ x := hc2_eq_q
        _ = c3 ◇ ((c2 ◇ x) ◇ x) := h146
        _ = c3 ◇ (c2 ◇ x) := congrArg (fun z : α => c3 ◇ z) hq_x
    exact hx_ne_c2 (hc2_eq_s.trans hs).symm
  constructor
  · intro hs
    have h135 : c2 ◇ x = c2 ◇ ((c2 ◇ x) ◇ (c1 ◇ c2)) := by
      simpa only [hpacket2] using h (c2 ◇ x) c2
    have h136 : c2 ◇ x = c3 ◇ ((c2 ◇ x) ◇ (c1 ◇ c3)) := by
      simpa only [hs] using h (c2 ◇ x) c3
    have hx_eq_qc13 : x = (c2 ◇ x) ◇ (c1 ◇ c3) := by
      apply p_left_cancel h c3
      calc
        c3 ◇ x = c2 ◇ x := hcollision.symm
        _ = c3 ◇ ((c2 ◇ x) ◇ (c1 ◇ c3)) := h136
    have hx_eq_qc12 : x = (c2 ◇ x) ◇ (c1 ◇ c2) := by
      apply p_left_cancel h c2
      calc
        c2 ◇ x = c2 ◇ x := rfl
        _ = c2 ◇ ((c2 ◇ x) ◇ (c1 ◇ c2)) := h135
    have hc1c2_eq_c1c3 : c1 ◇ c2 = c1 ◇ c3 := by
      apply p_left_cancel h (c2 ◇ x)
      exact hx_eq_qc12.symm.trans hx_eq_qc13
    exact hc2_ne_c3 (p_left_cancel h c1 hc1c2_eq_c1c3)
  constructor
  · intro hs
    have h146 : c3 = x ◇ (c3 ◇ c1) := by
      simpa only [hcycle, hc1] using h c3 x
    have hc2_eq_c3c1 : c2 = c3 ◇ c1 := by
      apply p_left_cancel h x
      exact hc3.trans h146
    have hq_eq_c1 : c2 ◇ x = c1 := by
      apply p_left_cancel h c3
      exact hs.trans hc2_eq_c3c1
    have hx_eq_q : x = c2 ◇ x := by
      apply p_left_cancel h c2
      calc
        c2 ◇ x = c2 ◇ x := rfl
        _ = c1 := hq_eq_c1
        _ = c2 ◇ (c2 ◇ x) := hpacket2.symm
    exact hx_ne_c1 (hx_eq_q.trans hq_eq_c1)
  · intro hs
    have hq_eq_x : c2 ◇ x = x := by
      apply p_left_cancel h c3
      calc
        c3 ◇ (c2 ◇ x) = c2 ◇ x := hs
        _ = c3 ◇ x := hcollision
    have hx_eq_c1 : x = c1 := by
      calc
        x = c2 ◇ x := hq_eq_x.symm
        _ = c2 ◇ (c2 ◇ x) := congrArg (fun z : α => c2 ◇ z) hq_eq_x.symm
        _ = c1 := hpacket2
    exact hx_ne_c1 hx_eq_c1

private structure CanonicalGrowthPacket (x c1 c2 c3 : α) : Prop where
  q_ne_x : c2 ◇ x ≠ x
  q_ne_c1 : c2 ◇ x ≠ c1
  q_ne_c2 : c2 ◇ x ≠ c2
  q_ne_c3 : c2 ◇ x ≠ c3
  branch :
    (c1 ◇ c2 ≠ x ∧
      c1 ◇ c2 ≠ c1 ∧
      c1 ◇ c2 ≠ c2 ∧
      c1 ◇ c2 ≠ c3 ∧
      c1 ◇ c2 ≠ c2 ◇ x) ∨
    (c1 ◇ c2 = c1 ∧
      c3 ◇ (c2 ◇ x) ≠ x ∧
      c3 ◇ (c2 ◇ x) ≠ c1 ∧
      c3 ◇ (c2 ◇ x) ≠ c2 ∧
      c3 ◇ (c2 ◇ x) ≠ c3 ∧
      c3 ◇ (c2 ◇ x) ≠ c2 ◇ x)

private theorem d4_q_joint_degeneracy_implies_x_eq_c3 [Finite α]
    (h : PE677 α) {x c1 c2 c3 : α}
    (hcollision : c2 ◇ x = c3 ◇ x)
    (hpacket1 : c1 ◇ (c2 ◇ x) = x)
    (hpacket2 : c2 ◇ (c2 ◇ x) = c1)
    (hr : c1 ◇ c2 = c1)
    (hs : c3 ◇ (c2 ◇ x) = c3) :
    x = c3 := by
  have hcancel : ∀ (a b c : α), a ◇ b = a ◇ c → b = c :=
    fun a _ _ hab => p_left_cancel h a hab
  have hx_qc1 : x = (c2 ◇ x) ◇ c1 := by
    apply hcancel c2
    calc
      c2 ◇ x = c2 ◇ ((c2 ◇ x) ◇ ((c2 ◇ (c2 ◇ x)) ◇ c2)) :=
        h (c2 ◇ x) c2
      _ = c2 ◇ ((c2 ◇ x) ◇ c1) := by rw [hpacket2, hr]
  have hx_qc33 : x = (c2 ◇ x) ◇ (c3 ◇ c3) := by
    apply hcancel c3
    calc
      c3 ◇ x = c3 ◇ ((c3 ◇ x) ◇ ((c3 ◇ (c3 ◇ x)) ◇ c3)) :=
        h (c3 ◇ x) c3
      _ = c3 ◇ ((c2 ◇ x) ◇ ((c3 ◇ (c2 ◇ x)) ◇ c3)) := by
        rw [← hcollision]
      _ = c3 ◇ ((c2 ◇ x) ◇ (c3 ◇ c3)) := by rw [hs]
  have hc1_c33 : c1 = c3 ◇ c3 := by
    apply hcancel (c2 ◇ x)
    exact hx_qc1.symm.trans hx_qc33
  have hq_expr : c2 ◇ x = c3 ◇ (c1 ◇ c3) := by
    apply hcancel c3
    calc
      c3 ◇ (c2 ◇ x) = c3 := hs
      _ = c3 ◇ (c3 ◇ ((c3 ◇ c3) ◇ c3)) := h c3 c3
      _ = c3 ◇ (c3 ◇ (c1 ◇ c3)) := by rw [← hc1_c33]
  have hx_c1c3 : x = c1 ◇ c3 := by
    apply hcancel c3
    calc
      c3 ◇ x = c2 ◇ x := hcollision.symm
      _ = c3 ◇ (c1 ◇ c3) := hq_expr
  have hq_c3 : c2 ◇ x = c3 := by
    apply hcancel c1
    calc
      c1 ◇ (c2 ◇ x) = x := hpacket1
      _ = c1 ◇ c3 := hx_c1c3
  have hc3x : c3 ◇ x = c3 := hcollision.symm.trans hq_c3
  have hc3c3 : c3 ◇ c3 = c3 := by simpa only [hq_c3] using hs
  exact hcancel c3 x c3 (hc3x.trans hc3c3.symm)

private theorem d4_q_canonicalGrowthPacket [Finite α]
    (h : PE677 α) {x c1 c2 c3 : α}
    (hc1 : x ◇ x = c1)
    (hc2 : x ◇ c1 = c2)
    (hc3 : x ◇ c2 = c3)
    (hcycle : x ◇ c3 = x)
    (hcollision : c2 ◇ x = c3 ◇ x)
    (hpacket1 : c1 ◇ (c2 ◇ x) = x)
    (hpacket2 : c2 ◇ (c2 ◇ x) = c1)
    (hx_ne_c1 : x ≠ c1)
    (hx_ne_c2 : x ≠ c2)
    (hx_ne_c3 : x ≠ c3)
    (hc1_ne_c2 : c1 ≠ c2)
    (hc2_ne_c3 : c2 ≠ c3) :
    CanonicalGrowthPacket x c1 c2 c3 := by
  have hqFresh := d4_q_ne_x_c1_c2 h hc2 hpacket2 hx_ne_c1
  have hq_ne_c3 : c2 ◇ x ≠ c3 := by
    exact q_packet_ne_c3 h x c1 c2 c3 (c2 ◇ x)
      hc1 hc2 hc3 hcycle rfl hpacket1 hpacket2 hc2_ne_c3
  refine ⟨hqFresh.1, hqFresh.2.1, hqFresh.2.2, hq_ne_c3, ?_⟩
  by_cases hr : c1 ◇ c2 = c1
  · right
    have hf := d4_q_s_partial_freshness h hc1 hc3 hcycle hcollision
      hpacket2 hx_ne_c1 hx_ne_c2 hc2_ne_c3
    have hs_ne_c3 : c3 ◇ (c2 ◇ x) ≠ c3 := by
      intro hs
      exact hx_ne_c3 <|
        d4_q_joint_degeneracy_implies_x_eq_c3 h hcollision hpacket1
          hpacket2 hr hs
    exact ⟨hr, hf.1, hf.2.1, hf.2.2.1, hs_ne_c3, hf.2.2.2⟩
  · left
    have hf := d4_q_r_partial_freshness h hc1 hc2 hcollision hpacket1
      hpacket2 hx_ne_c1 hx_ne_c2 hc1_ne_c2
    exact ⟨hf.1, hr, hf.2.1, hf.2.2.1, hf.2.2.2⟩

private theorem orbitQ_d4_canonicalGrowthPacket [Finite α]
    (h : PE677 α) (x : α)
    (hperiod : orbitPoint x 4 = x)
    (hx_ne_c1 : x ≠ orbitPoint x 1)
    (hx_ne_c2 : x ≠ orbitPoint x 2)
    (hx_ne_c3 : x ≠ orbitPoint x 3)
    (hc1_ne_c2 : orbitPoint x 1 ≠ orbitPoint x 2)
    (hc2_ne_c3 : orbitPoint x 2 ≠ orbitPoint x 3)
    (hcollision : orbitQ x 1 0 = orbitQ x 2 1) :
    CanonicalGrowthPacket x (orbitPoint x 1) (orbitPoint x 2) (orbitPoint x 3) := by
  apply d4_q_canonicalGrowthPacket h
  · simp [orbitPoint]
  · simp [orbitPoint]
  · simp [orbitPoint]
  · simpa [orbitPoint] using hperiod
  · calc
      orbitPoint x 2 ◇ x = orbitQ x 1 0 :=
        (orbitQ_subdiag_eq_rightMul h x 0).symm
      _ = orbitQ x 2 1 := hcollision
      _ = orbitPoint x 3 ◇ x :=
        orbitQ_subdiag_eq_rightMul h x 1
  · calc
      orbitPoint x 1 ◇ (orbitPoint x 2 ◇ x) =
          orbitPoint x 1 ◇ orbitQ x 1 0 := by
            rw [orbitQ_subdiag_eq_rightMul h x 0]
      _ = x := by
        simpa [orbitPoint] using orbitQ_spec_bare h x 1 0
  · calc
      orbitPoint x 2 ◇ (orbitPoint x 2 ◇ x) =
          orbitPoint x 2 ◇ orbitQ x 1 0 := by
            rw [orbitQ_subdiag_eq_rightMul h x 0]
      _ = orbitPoint x 2 ◇ orbitQ x 2 1 :=
        congrArg (fun z => orbitPoint x 2 ◇ z) hcollision
      _ = orbitPoint x 1 := orbitQ_spec_bare h x 2 1
  · exact hx_ne_c1
  · exact hx_ne_c2
  · exact hx_ne_c3
  · exact hc1_ne_c2
  · exact hc2_ne_c3

private def OtherPairCollision (x : α) : Prop :=
  orbitQ x 1 0 = orbitQ x 3 2 ∨
    orbitQ x 1 0 = orbitQ x 4 3 ∨
    orbitQ x 2 1 = orbitQ x 3 2 ∨
    orbitQ x 2 1 = orbitQ x 4 3 ∨
    orbitQ x 3 2 = orbitQ x 4 3

private theorem iterate_eq_self_of_period_mul {β : Type u}
    (f : β → β) (x : β) (d : ℕ) (hperiod : f^[d] x = x) :
    ∀ q : ℕ, f^[d * q] x = x
  | 0 => by simp
  | q + 1 => by
      rw [Nat.mul_succ, Function.iterate_add_apply, hperiod]
      exact iterate_eq_self_of_period_mul f x d hperiod q

private theorem iterate_mod_of_periodic_point {β : Type u}
    (f : β → β) (x : β) (d n : ℕ) (hperiod : f^[d] x = x) :
    f^[n % d] x = f^[n] x := by
  have hmul : f^[d * (n / d)] x = x :=
    iterate_eq_self_of_period_mul f x d hperiod (n / d)
  calc
    f^[n % d] x = f^[n % d] (f^[d * (n / d)] x) := by rw [hmul]
    _ = f^[n % d + d * (n / d)] x := by
      rw [← Function.iterate_add_apply]
    _ = f^[n] x := by rw [Nat.mod_add_div]

private theorem orbitPoint_mod_four (x : α) (n : ℕ)
    (hperiod : orbitPoint x 4 = x) :
    orbitPoint x (n % 4) = orbitPoint x n := by
  unfold orbitPoint at hperiod ⊢
  exact iterate_mod_of_periodic_point (fun z => x ◇ z) x 4 n hperiod

private theorem d4_indexed_collision_pair_classifier [Finite α]
    (h : PE677 α) (x : α) (m n : ℕ)
    (hperiod : orbitPoint x 4 = x)
    (hsources_ne : orbitPoint x m ≠ orbitPoint x n)
    (hcollision : orbitPoint x m ◇ x = orbitPoint x n ◇ x) :
    orbitQ x 1 0 = orbitQ x 2 1 ∨ OtherPairCollision x := by
  have hmred := orbitPoint_mod_four x m hperiod
  have hnred := orbitPoint_mod_four x n hperiod
  have hsources_mod_ne : orbitPoint x (m % 4) ≠ orbitPoint x (n % 4) := by
    intro heq
    exact hsources_ne (hmred.symm.trans (heq.trans hnred))
  have hcollision_mod : orbitPoint x (m % 4) ◇ x = orbitPoint x (n % 4) ◇ x := by
    calc
      orbitPoint x (m % 4) ◇ x = orbitPoint x m ◇ x :=
        congrArg (fun z => z ◇ x) hmred
      _ = orbitPoint x n ◇ x := hcollision
      _ = orbitPoint x (n % 4) ◇ x :=
        congrArg (fun z => z ◇ x) hnred.symm
  have hR0 : orbitPoint x 0 ◇ x = orbitQ x 3 2 := by
    calc
      orbitPoint x 0 ◇ x = orbitPoint x 4 ◇ x := by
        simpa [orbitPoint] using congrArg (fun z => z ◇ x) hperiod.symm
      _ = orbitQ x 3 2 := (orbitQ_subdiag_eq_rightMul h x 2).symm
  have hR1 : orbitPoint x 1 ◇ x = orbitQ x 4 3 := by
    have h15 : orbitPoint x 1 = orbitPoint x 5 := by
      simpa using orbitPoint_mod_four x 5 hperiod
    calc
      orbitPoint x 1 ◇ x = orbitPoint x 5 ◇ x :=
        congrArg (fun z => z ◇ x) h15
      _ = orbitQ x 4 3 := (orbitQ_subdiag_eq_rightMul h x 3).symm
  have hR2 : orbitPoint x 2 ◇ x = orbitQ x 1 0 :=
    (orbitQ_subdiag_eq_rightMul h x 0).symm
  have hR3 : orbitPoint x 3 ◇ x = orbitQ x 2 1 :=
    (orbitQ_subdiag_eq_rightMul h x 1).symm
  have hm_cases : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by
    omega
  have hn_cases : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by
    omega
  rcases hm_cases with hm0 | hm1 | hm2 | hm3 <;>
    rcases hn_cases with hn0 | hn1 | hn2 | hn3
  · exact (hsources_mod_ne (by rw [hm0, hn0])).elim
  · right; exact Or.inr (Or.inr (Or.inr (Or.inr (by
      simpa only [hm0, hn1, hR0, hR1] using hcollision_mod))))
  · right; exact Or.inl (by
      simpa only [hm0, hn2, hR0, hR2] using hcollision_mod.symm)
  · right; exact Or.inr (Or.inr (Or.inl (by
      simpa only [hm0, hn3, hR0, hR3] using hcollision_mod.symm)))
  · right; exact Or.inr (Or.inr (Or.inr (Or.inr (by
      simpa only [hm1, hn0, hR1, hR0] using hcollision_mod.symm))))
  · exact (hsources_mod_ne (by rw [hm1, hn1])).elim
  · right; exact Or.inr (Or.inl (by
      simpa only [hm1, hn2, hR1, hR2] using hcollision_mod.symm))
  · right; exact Or.inr (Or.inr (Or.inr (Or.inl (by
      simpa only [hm1, hn3, hR1, hR3] using hcollision_mod.symm))))
  · right; exact Or.inl (by
      simpa only [hm2, hn0, hR2, hR0] using hcollision_mod)
  · right; exact Or.inr (Or.inl (by
      simpa only [hm2, hn1, hR2, hR1] using hcollision_mod))
  · exact (hsources_mod_ne (by rw [hm2, hn2])).elim
  · left; simpa only [hm2, hn3, hR2, hR3] using hcollision_mod
  · right; exact Or.inr (Or.inr (Or.inl (by
      simpa only [hm3, hn0, hR3, hR0] using hcollision_mod)))
  · right; exact Or.inr (Or.inr (Or.inr (Or.inl (by
      simpa only [hm3, hn1, hR3, hR1] using hcollision_mod))))
  · left; simpa only [hm3, hn2, hR3, hR2] using hcollision_mod.symm
  · exact (hsources_mod_ne (by rw [hm3, hn3])).elim

private theorem otherPairs_qCollision_star [Finite α]
    (h : PE677 α) (x : α) {i j : ℕ}
    (hq : orbitQ x (i + 1) i = orbitQ x (j + 1) j) :
    (orbitPoint x (i + 2) ◇ (orbitPoint x (i + 2) ◇ x)) ◇ orbitPoint x (i + 2) =
      (orbitPoint x (j + 2) ◇ (orbitPoint x (j + 2) ◇ x)) ◇ orbitPoint x (j + 2) := by
  have heq : orbitPoint x (i + 2) ◇ x = orbitPoint x (j + 2) ◇ x := by
    rw [← orbitQ_subdiag_eq_rightMul h x i, ← orbitQ_subdiag_eq_rightMul h x j]
    exact hq
  have hi :
      x = (orbitPoint x (i + 2) ◇ x) ◇
        ((orbitPoint x (i + 2) ◇ (orbitPoint x (i + 2) ◇ x)) ◇ orbitPoint x (i + 2)) := by
    apply p_left_cancel h (orbitPoint x (i + 2))
    exact h (orbitPoint x (i + 2) ◇ x) (orbitPoint x (i + 2))
  have hj :
      x = (orbitPoint x (j + 2) ◇ x) ◇
        ((orbitPoint x (j + 2) ◇ (orbitPoint x (j + 2) ◇ x)) ◇ orbitPoint x (j + 2)) := by
    apply p_left_cancel h (orbitPoint x (j + 2))
    exact h (orbitPoint x (j + 2) ◇ x) (orbitPoint x (j + 2))
  rw [heq] at hi ⊢
  exact p_left_cancel h (orbitPoint x (j + 2) ◇ x) (hi.symm.trans hj)

private theorem orbitQ_d4_q2_eq_c1 [Finite α]
    (h : PE677 α) (x : α) (hperiod : orbitPoint x 4 = x) :
    orbitQ x 3 2 = orbitPoint x 1 := by
  calc
    orbitQ x 3 2 = orbitPoint x 4 ◇ x := orbitQ_subdiag_eq_rightMul h x 2
    _ = x ◇ x := by rw [hperiod]
    _ = orbitPoint x 1 := by simp [orbitPoint]

private theorem orbitQ_d4_q3_eq_c2 [Finite α]
    (h : PE677 α) (x : α) (hperiod : orbitPoint x 4 = x) :
    orbitQ x 4 3 = orbitPoint x 2 := by
  apply p_left_cancel h x
  calc
    x ◇ orbitQ x 4 3 = orbitPoint x 4 ◇ orbitQ x 4 3 := by rw [hperiod]
    _ = orbitPoint x 3 := orbitQ_spec_bare h x 4 3
    _ = x ◇ orbitPoint x 2 := by simp [orbitPoint]

private theorem orbitQ_d4_q1_eq_q2_false [Finite α]
    (h : PE677 α) (x : α)
    (hperiod : orbitPoint x 4 = x)
    (hx_ne_c3 : x ≠ orbitPoint x 3)
    (hq : orbitQ x 2 1 = orbitQ x 3 2) :
    False := by
  have hstar := otherPairs_qCollision_star h x (i := 1) (j := 2) hq
  have hq_eq_c1 : orbitQ x 2 1 = orbitPoint x 1 :=
    hq.trans (orbitQ_d4_q2_eq_c1 h x hperiod)
  have hc3_q : orbitPoint x 3 ◇ orbitQ x 2 1 = orbitPoint x 2 := by
    rw [hq]
    exact orbitQ_spec_bare h x 3 2
  have hbranch : orbitPoint x 3 ◇ x = orbitPoint x 1 := by
    calc
      orbitPoint x 3 ◇ x = orbitQ x 2 1 := (orbitQ_subdiag_eq_rightMul h x 1).symm
      _ = orbitPoint x 1 := hq_eq_c1
  have hc3c1 : orbitPoint x 3 ◇ orbitPoint x 1 = orbitPoint x 2 := by
    simpa [hq_eq_c1] using hc3_q
  change
    ((orbitPoint x 3 ◇ (orbitPoint x 3 ◇ x)) ◇ orbitPoint x 3) =
      ((orbitPoint x 4 ◇ (orbitPoint x 4 ◇ x)) ◇ orbitPoint x 4) at hstar
  have hleft : (orbitPoint x 2 ◇ orbitPoint x 3) = orbitPoint x 2 ◇ x := by
    rw [hbranch, hc3c1, hperiod] at hstar
    simpa [orbitPoint] using hstar
  exact hx_ne_c3 (p_left_cancel h (orbitPoint x 2) hleft).symm

private theorem orbitQ_d4_q2_eq_q3_false [Finite α]
    (h : PE677 α) (x : α)
    (hperiod : orbitPoint x 4 = x)
    (hc1_ne_c2 : orbitPoint x 1 ≠ orbitPoint x 2)
    (hq : orbitQ x 3 2 = orbitQ x 4 3) :
    False := by
  exact hc1_ne_c2 ((orbitQ_d4_q2_eq_c1 h x hperiod).symm.trans
    (hq.trans (orbitQ_d4_q3_eq_c2 h x hperiod)))

private theorem orbitQ_d4_q0_eq_q2_c3_fixer [Finite α]
    (h : PE677 α) (x : α)
    (hperiod : orbitPoint x 4 = x)
    (hq : orbitQ x 1 0 = orbitQ x 3 2) :
    orbitPoint x 3 ◇ x = x := by
  have hbranch : orbitPoint x 2 ◇ x = orbitPoint x 1 := by
    calc
      orbitPoint x 2 ◇ x = orbitQ x 1 0 := (orbitQ_subdiag_eq_rightMul h x 0).symm
      _ = orbitQ x 3 2 := hq
      _ = orbitPoint x 1 := orbitQ_d4_q2_eq_c1 h x hperiod
  have hE : orbitPoint x 2 = x ◇ (orbitPoint x 2 ◇ (orbitPoint x 3 ◇ x)) := by
    calc
      orbitPoint x 2 = x ◇ (orbitPoint x 2 ◇ ((x ◇ orbitPoint x 2) ◇ x)) :=
        h (orbitPoint x 2) x
      _ = x ◇ (orbitPoint x 2 ◇ (orbitPoint x 3 ◇ x)) := by
        simp [orbitPoint]
  have hc1_chain : orbitPoint x 1 = orbitPoint x 2 ◇ (orbitPoint x 3 ◇ x) := by
    apply p_left_cancel h x
    calc
      x ◇ orbitPoint x 1 = orbitPoint x 2 := by simp [orbitPoint]
      _ = x ◇ (orbitPoint x 2 ◇ (orbitPoint x 3 ◇ x)) := hE
  apply p_left_cancel h (orbitPoint x 2)
  exact (hbranch.trans hc1_chain).symm

private theorem orbitQ_d4_q0_eq_q3_false [Finite α]
    (h : PE677 α) (x : α)
    (hperiod : orbitPoint x 4 = x)
    (hc2_ne_c3 : orbitPoint x 2 ≠ orbitPoint x 3)
    (hq : orbitQ x 1 0 = orbitQ x 4 3) :
    False := by
  have hq0_eq_c2 : orbitQ x 1 0 = orbitPoint x 2 :=
    hq.trans (orbitQ_d4_q3_eq_c2 h x hperiod)
  have hbranch : orbitPoint x 2 ◇ x = orbitPoint x 2 := by
    exact (orbitQ_subdiag_eq_rightMul h x 0).symm.trans hq0_eq_c2
  have hc1c2 : orbitPoint x 1 ◇ orbitPoint x 2 = x := by
    calc
      orbitPoint x 1 ◇ orbitPoint x 2 = orbitPoint x 1 ◇ orbitQ x 1 0 := by
        rw [hq0_eq_c2]
      _ = x := by simpa [orbitPoint] using orbitQ_spec_bare h x 1 0
  have hstar := otherPairs_qCollision_star h x (i := 0) (j := 3) hq
  have hpoint5 : orbitPoint x 5 = orbitPoint x 1 := by
    change x ◇ orbitPoint x 4 = x ◇ x
    rw [hperiod]
  have hc1x : orbitPoint x 1 ◇ x = orbitPoint x 2 := by
    calc
      orbitPoint x 1 ◇ x = orbitPoint x 5 ◇ x := by rw [hpoint5]
      _ = orbitQ x 4 3 := (orbitQ_subdiag_eq_rightMul h x 3).symm
      _ = orbitPoint x 2 := orbitQ_d4_q3_eq_c2 h x hperiod
  have hxc1 : x ◇ orbitPoint x 1 = orbitPoint x 2 := by
    simp [orbitPoint]
  change
    ((orbitPoint x 2 ◇ (orbitPoint x 2 ◇ x)) ◇ orbitPoint x 2) =
      ((orbitPoint x 5 ◇ (orbitPoint x 5 ◇ x)) ◇ orbitPoint x 5) at hstar
  have hstar_local :
      (orbitPoint x 2 ◇ orbitPoint x 2) ◇ orbitPoint x 2 = orbitPoint x 2 := by
    rw [hbranch, hpoint5, hc1x, hc1c2, hxc1] at hstar
    exact hstar
  have hE : orbitPoint x 2 = orbitPoint x 2 ◇ (orbitPoint x 2 ◇ orbitPoint x 2) := by
    simpa only [hstar_local] using h (orbitPoint x 2) (orbitPoint x 2)
  have hx_eq_t : x = orbitPoint x 2 ◇ orbitPoint x 2 := by
    apply p_left_cancel h (orbitPoint x 2)
    exact hbranch.trans hE
  apply hc2_ne_c3
  calc
    orbitPoint x 2 = (orbitPoint x 2 ◇ orbitPoint x 2) ◇ orbitPoint x 2 :=
      hstar_local.symm
    _ = x ◇ orbitPoint x 2 := congrArg (fun z ↦ z ◇ orbitPoint x 2) hx_eq_t.symm
    _ = orbitPoint x 3 := by simp [orbitPoint]

private theorem orbitQ_d4_q1_eq_q3_false [Finite α]
    (h : PE677 α) (x : α)
    (hperiod : orbitPoint x 4 = x)
    (hx_ne_c1 : x ≠ orbitPoint x 1)
    (hq : orbitQ x 2 1 = orbitQ x 4 3) :
    False := by
  have hbranch : orbitPoint x 3 ◇ x = orbitPoint x 2 := by
    calc
      orbitPoint x 3 ◇ x = orbitQ x 2 1 := (orbitQ_subdiag_eq_rightMul h x 1).symm
      _ = orbitQ x 4 3 := hq
      _ = orbitPoint x 2 := orbitQ_d4_q3_eq_c2 h x hperiod
  have hE : orbitPoint x 3 = x ◇ (orbitPoint x 3 ◇ orbitPoint x 1) := by
    have hxc3 : x ◇ orbitPoint x 3 = x := by
      simpa [orbitPoint] using hperiod
    calc
      orbitPoint x 3 = x ◇ (orbitPoint x 3 ◇ ((x ◇ orbitPoint x 3) ◇ x)) :=
        h (orbitPoint x 3) x
      _ = x ◇ (orbitPoint x 3 ◇ (x ◇ x)) := by rw [hxc3]
      _ = x ◇ (orbitPoint x 3 ◇ orbitPoint x 1) := by simp [orbitPoint]
  have hc2_eq : orbitPoint x 2 = orbitPoint x 3 ◇ orbitPoint x 1 := by
    apply p_left_cancel h x
    calc
      x ◇ orbitPoint x 2 = orbitPoint x 3 := by simp [orbitPoint]
      _ = x ◇ (orbitPoint x 3 ◇ orbitPoint x 1) := hE
  apply hx_ne_c1
  apply p_left_cancel h (orbitPoint x 3)
  exact hbranch.trans hc2_eq

private theorem d4_otherPairCollision_hasFixer [Finite α]
    (h : PE677 α) (x : α)
    (hperiod : orbitPoint x 4 = x)
    (hx_ne_c1 : x ≠ orbitPoint x 1)
    (hx_ne_c3 : x ≠ orbitPoint x 3)
    (hc1_ne_c2 : orbitPoint x 1 ≠ orbitPoint x 2)
    (hc2_ne_c3 : orbitPoint x 2 ≠ orbitPoint x 3)
    (hother : OtherPairCollision x) :
    PHasFixerAt x := by
  rcases hother with h02 | h03 | h12 | h13 | h23
  · exact ⟨orbitPoint x 3, orbitQ_d4_q0_eq_q2_c3_fixer h x hperiod h02⟩
  · exact (orbitQ_d4_q0_eq_q3_false h x hperiod hc2_ne_c3 h03).elim
  · exact (orbitQ_d4_q1_eq_q2_false h x hperiod hx_ne_c3 h12).elim
  · exact (orbitQ_d4_q1_eq_q3_false h x hperiod hx_ne_c1 h13).elim
  · exact (orbitQ_d4_q2_eq_q3_false h x hperiod hc1_ne_c2 h23).elim

private structure DistinguishedPacket (x c1 c2 c3 : α) : Prop where
  q_collision : c2 ◇ x = c3 ◇ x
  q_packet_preimage : c1 ◇ (c2 ◇ x) = x
  q_packet_return : c2 ◇ (c2 ◇ x) = c1
  canonical_growth : CanonicalGrowthPacket x c1 c2 c3

private theorem minimalPeriodFour_distinctness [Finite α]
    (h : PE677 α) (x : α) (hperiod : PMinimalOrbitPeriod x 4) :
    x ≠ orbitPoint x 1 ∧ x ≠ orbitPoint x 2 ∧ x ≠ orbitPoint x 3 ∧
      orbitPoint x 1 ≠ orbitPoint x 2 ∧ orbitPoint x 1 ≠ orbitPoint x 3 ∧
      orbitPoint x 2 ≠ orbitPoint x 3 := by
  have hminimal := hperiod.2.2
  have hx_ne_c1 : x ≠ orbitPoint x 1 := by
    intro heq
    have := hminimal 1 (by omega) heq.symm
    omega
  have hx_ne_c2 : x ≠ orbitPoint x 2 := by
    intro heq
    have := hminimal 2 (by omega) heq.symm
    omega
  have hx_ne_c3 : x ≠ orbitPoint x 3 := by
    intro heq
    have := hminimal 3 (by omega) heq.symm
    omega
  have hc1_ne_c2 : orbitPoint x 1 ≠ orbitPoint x 2 := by
    intro heq
    exact hx_ne_c1 (p_left_cancel h x heq)
  have hc2_ne_c3 : orbitPoint x 2 ≠ orbitPoint x 3 := by
    intro heq
    exact hc1_ne_c2 (p_left_cancel h x heq)
  have hc1_ne_c3 : orbitPoint x 1 ≠ orbitPoint x 3 := by
    intro heq
    exact hx_ne_c2 (p_left_cancel h x heq)
  exact ⟨hx_ne_c1, hx_ne_c2, hx_ne_c3, hc1_ne_c2, hc1_ne_c3, hc2_ne_c3⟩

private theorem orbitQ_d4_distinguishedPacket [Finite α]
    (h : PE677 α) (x : α)
    (hperiod : orbitPoint x 4 = x)
    (hx_ne_c1 : x ≠ orbitPoint x 1)
    (hx_ne_c2 : x ≠ orbitPoint x 2)
    (hx_ne_c3 : x ≠ orbitPoint x 3)
    (hc1_ne_c2 : orbitPoint x 1 ≠ orbitPoint x 2)
    (hc2_ne_c3 : orbitPoint x 2 ≠ orbitPoint x 3)
    (hcollision : orbitQ x 1 0 = orbitQ x 2 1) :
    DistinguishedPacket x (orbitPoint x 1) (orbitPoint x 2) (orbitPoint x 3) := by
  have hq_collision : orbitPoint x 2 ◇ x = orbitPoint x 3 ◇ x := by
    calc
      orbitPoint x 2 ◇ x = orbitQ x 1 0 := (orbitQ_subdiag_eq_rightMul h x 0).symm
      _ = orbitQ x 2 1 := hcollision
      _ = orbitPoint x 3 ◇ x := orbitQ_subdiag_eq_rightMul h x 1
  have hq_packet_preimage : orbitPoint x 1 ◇ (orbitPoint x 2 ◇ x) = x := by
    calc
      orbitPoint x 1 ◇ (orbitPoint x 2 ◇ x) = orbitPoint x 1 ◇ orbitQ x 1 0 := by
        rw [orbitQ_subdiag_eq_rightMul h x 0]
      _ = x := by simpa [orbitPoint] using orbitQ_spec_bare h x 1 0
  have hq_packet_return :
      orbitPoint x 2 ◇ (orbitPoint x 2 ◇ x) = orbitPoint x 1 := by
    calc
      orbitPoint x 2 ◇ (orbitPoint x 2 ◇ x) = orbitPoint x 2 ◇ orbitQ x 1 0 := by
        rw [orbitQ_subdiag_eq_rightMul h x 0]
      _ = orbitPoint x 2 ◇ orbitQ x 2 1 :=
        congrArg (fun z ↦ orbitPoint x 2 ◇ z) hcollision
      _ = orbitPoint x 1 := orbitQ_spec_bare h x 2 1
  exact ⟨hq_collision, hq_packet_preimage, hq_packet_return,
    orbitQ_d4_canonicalGrowthPacket h x hperiod hx_ne_c1 hx_ne_c2 hx_ne_c3
      hc1_ne_c2 hc2_ne_c3 hcollision⟩

private theorem minimalPeriodFour_orbitRightCollision_distinguishedPacket_or_hasFixer
    [Finite α]
    (h : PE677 α) (x : α)
    (hperiod : PMinimalOrbitPeriod x 4)
    {a b : α}
    (ha : ∃ i : ℕ, a = orbitPoint x i)
    (hb : ∃ j : ℕ, b = orbitPoint x j)
    (hsources_ne : a ≠ b)
    (hcollision : a ◇ x = b ◇ x) :
    DistinguishedPacket x (orbitPoint x 1) (orbitPoint x 2) (orbitPoint x 3) ∨
      PHasFixerAt x := by
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  have hcloses := hperiod.2.1
  change orbitPoint x 4 = x at hcloses
  rcases minimalPeriodFour_distinctness h x hperiod with
    ⟨hx_ne_c1, hx_ne_c2, hx_ne_c3, hc1_ne_c2, _, hc2_ne_c3⟩
  rcases d4_indexed_collision_pair_classifier h x i j hcloses hsources_ne hcollision with
    hdistinguished | hother
  · exact Or.inl (orbitQ_d4_distinguishedPacket h x hcloses hx_ne_c1 hx_ne_c2 hx_ne_c3
      hc1_ne_c2 hc2_ne_c3 hdistinguished)
  · exact Or.inr (d4_otherPairCollision_hasFixer h x hcloses hx_ne_c1 hx_ne_c3
      hc1_ne_c2 hc2_ne_c3 hother)

end Port

theorem solution
    {α : Type u} [Fintype α] (op : α → α → α) (h : FiniteMagmaE677.E677 op)
    (x c1 c2 c3 : α)
    (hc1 : op x x = c1)
    (hc2 : op x c1 = c2)
    (hc3 : op x c2 = c3)
    (hcloses : op x c3 = x)
    (hx_ne_c1 : x ≠ c1)
    (hx_ne_c2 : x ≠ c2)
    (hx_ne_c3 : x ≠ c3)
    (a b : α)
    (ha : FiniteMagmaE677.InLeftOrbit op x a)
    (hb : FiniteMagmaE677.InLeftOrbit op x b)
    (hab : a ≠ b)
    (hcollision : op a x = op b x) :
    (op c2 x = op c3 x ∧
      op c1 (op c2 x) = x ∧
      op c2 (op c2 x) = c1 ∧
      op c2 x ≠ x ∧
      op c2 x ≠ c1 ∧
      op c2 x ≠ c2 ∧
      op c2 x ≠ c3 ∧
      ((op c1 c2 ≠ x ∧
          op c1 c2 ≠ c1 ∧
          op c1 c2 ≠ c2 ∧
          op c1 c2 ≠ c3 ∧
          op c1 c2 ≠ op c2 x) ∨
        (op c1 c2 = c1 ∧
          op c3 (op c2 x) ≠ x ∧
          op c3 (op c2 x) ≠ c1 ∧
          op c3 (op c2 x) ≠ c2 ∧
          op c3 (op c2 x) ≠ c3 ∧
          op c3 (op c2 x) ≠ op c2 x))) ∨
      FiniteMagmaE677.HasFixerAt op x := by
  letI : PMagma α := ⟨op⟩
  have h' : PE677 α := fun u v => h u v
  subst hc3 hc2 hc1
  have hperiod : PMinimalOrbitPeriod x 4 := by
    refine ⟨by norm_num, hcloses, ?_⟩
    intro e he hfix
    by_contra hlt
    interval_cases e
    · exact hx_ne_c1 hfix.symm
    · exact hx_ne_c2 hfix.symm
    · exact hx_ne_c3 hfix.symm
  rcases minimalPeriodFour_orbitRightCollision_distinguishedPacket_or_hasFixer
      h' x hperiod ha hb hab hcollision with p | hfix
  · exact Or.inl ⟨p.q_collision, p.q_packet_preimage, p.q_packet_return,
      p.canonical_growth.q_ne_x, p.canonical_growth.q_ne_c1,
      p.canonical_growth.q_ne_c2, p.canonical_growth.q_ne_c3,
      p.canonical_growth.branch⟩
  · exact Or.inr hfix
