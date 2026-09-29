-- Prove2me | solution 1 for FiniteMagmaE677.period_four_swapped_s_q_square_refinement
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-24T08:36:59.424368+00:00
-- url     : https://prove2.me/submissions/5ab30a32-eab4-4bab-9de3-41295a07e9a7

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Definitions.Def_FiniteMagmaE677_sswap_renewal
import Mathlib

section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna.
-/

/-!
# S-swap source compatibility proofs

All proofs here are stated over the isolated class in `Definitions.Base` and
reduce to the published explicit-operation first-return definitions.
-/

namespace FiniteMagmaE677.SSwap
local infixl:65 " ◇ " => Magma'.op

universe u


theorem e677_leftMul_surj {α : Type u} [Magma' α]
    (h : E677 (α := α)) (y : α) :
    Function.Surjective (fun z : α => y ◇ z) := by
  intro z
  exact ⟨z ◇ ((y ◇ z) ◇ y), (h z y).symm⟩

theorem e677_leftMul_inj {α : Type u} [Fintype α] [Magma' α]
    (h : E677 (α := α)) (y : α) :
    Function.Injective (fun z : α => y ◇ z) := by
  exact (Finite.surjective_iff_bijective.mp (e677_leftMul_surj h y)).1

theorem e677_left_cancel {α : Type u} [Fintype α] [Magma' α]
    (h : E677 (α := α)) (y : α) {a b : α}
    (hab : y ◇ a = y ◇ b) : a = b :=
  e677_leftMul_inj h y hab

theorem e677_backward_recurrence {α : Type u} [Fintype α] [Magma' α]
    (h : E677 (α := α)) (x y : α) :
    x = (y ◇ x) ◇ ((y ◇ (y ◇ x)) ◇ y) := by
  have h1 : y ◇ x = y ◇ ((y ◇ x) ◇ ((y ◇ (y ◇ x)) ◇ y)) :=
    h (y ◇ x) y
  exact e677_left_cancel h y h1

theorem e677_fixer_unique {α : Type u} [Fintype α] [Magma' α]
    (h : E677 (α := α)) {x y : α}
    (hfix : y ◇ x = x) : y = (x ◇ x) ◇ x := by
  have inv_at_x : y ◇ (x ◇ (x ◇ y)) = x := by
    have h0 : y ◇ (x ◇ ((y ◇ x) ◇ y)) = x := (h x y).symm
    simpa only [hfix] using h0
  have hx_xy := e677_left_cancel h y (hfix.trans inv_at_x.symm)
  exact e677_left_cancel h x (e677_left_cancel h x
    (hx_xy.symm.trans (h x x)))

theorem d4Trace_next_eq_seed_or_extend
    {α : Type u} {op : α → α → α} {x c1 c2 c3 seed : α} {n : ℕ}
    (leftInjective : Function.Injective (op x))
    (hxc1 : op x x = c1) (hc1c2 : op x c1 = c2)
    (hc2c3 : op x c2 = c3) (hc3x : op x c3 = x)
    (htrace : FiniteMagmaE677.FirstReturn.D4Trace op x c1 c2 c3 seed n) :
    FiniteMagmaE677.FirstReturn.orbitPoint op x (n + 1) seed = seed ∨
      FiniteMagmaE677.FirstReturn.D4Trace op x c1 c2 c3 seed (n + 1) := by
  let f : α → α := op x
  have hnext_step : f (FiniteMagmaE677.FirstReturn.orbitPoint op x n seed) =
      FiniteMagmaE677.FirstReturn.orbitPoint op x (n + 1) seed := by
    exact (Function.iterate_succ_apply' f n seed).symm
  by_cases hreturn : FiniteMagmaE677.FirstReturn.orbitPoint op x (n + 1) seed = seed
  · exact Or.inl hreturn
  · right
    have hnext_ne_x :
        FiniteMagmaE677.FirstReturn.orbitPoint op x (n + 1) seed ≠ x := by
      intro heq
      have hn_eq_c3 : FiniteMagmaE677.FirstReturn.orbitPoint op x n seed = c3 := by
        apply leftInjective
        calc
          f (FiniteMagmaE677.FirstReturn.orbitPoint op x n seed) =
              FiniteMagmaE677.FirstReturn.orbitPoint op x (n + 1) seed := hnext_step
          _ = x := heq
          _ = f c3 := by simpa [f] using hc3x.symm
      exact (htrace.outside n le_rfl).2.2.2 hn_eq_c3
    have hnext_ne_c1 :
        FiniteMagmaE677.FirstReturn.orbitPoint op x (n + 1) seed ≠ c1 := by
      intro heq
      have hn_eq_x : FiniteMagmaE677.FirstReturn.orbitPoint op x n seed = x := by
        apply leftInjective
        calc
          f (FiniteMagmaE677.FirstReturn.orbitPoint op x n seed) =
              FiniteMagmaE677.FirstReturn.orbitPoint op x (n + 1) seed := hnext_step
          _ = c1 := heq
          _ = f x := by simpa [f] using hxc1.symm
      exact (htrace.outside n le_rfl).1 hn_eq_x
    have hnext_ne_c2 :
        FiniteMagmaE677.FirstReturn.orbitPoint op x (n + 1) seed ≠ c2 := by
      intro heq
      have hn_eq_c1 : FiniteMagmaE677.FirstReturn.orbitPoint op x n seed = c1 := by
        apply leftInjective
        calc
          f (FiniteMagmaE677.FirstReturn.orbitPoint op x n seed) =
              FiniteMagmaE677.FirstReturn.orbitPoint op x (n + 1) seed := hnext_step
          _ = c2 := heq
          _ = f c1 := by simpa [f] using hc1c2.symm
      exact (htrace.outside n le_rfl).2.1 hn_eq_c1
    have hnext_ne_c3 :
        FiniteMagmaE677.FirstReturn.orbitPoint op x (n + 1) seed ≠ c3 := by
      intro heq
      have hn_eq_c2 : FiniteMagmaE677.FirstReturn.orbitPoint op x n seed = c2 := by
        apply leftInjective
        calc
          f (FiniteMagmaE677.FirstReturn.orbitPoint op x n seed) =
              FiniteMagmaE677.FirstReturn.orbitPoint op x (n + 1) seed := hnext_step
          _ = c3 := heq
          _ = f c2 := by simpa [f] using hc2c3.symm
      exact (htrace.outside n le_rfl).2.2.1 hn_eq_c2
    have hnext_ne_prior : ∀ i, i ≤ n →
        FiniteMagmaE677.FirstReturn.orbitPoint op x (n + 1) seed ≠
          FiniteMagmaE677.FirstReturn.orbitPoint op x i seed := by
      intro i hi heq
      cases i with
      | zero => exact hreturn heq
      | succ k =>
          have hk : k ≤ n := by omega
          have hn_eq_hk :
              FiniteMagmaE677.FirstReturn.orbitPoint op x n seed =
                FiniteMagmaE677.FirstReturn.orbitPoint op x k seed := by
            apply leftInjective
            calc
              f (FiniteMagmaE677.FirstReturn.orbitPoint op x n seed) =
                  FiniteMagmaE677.FirstReturn.orbitPoint op x (n + 1) seed := hnext_step
              _ = FiniteMagmaE677.FirstReturn.orbitPoint op x (Nat.succ k) seed := heq
              _ = f (FiniteMagmaE677.FirstReturn.orbitPoint op x k seed) :=
                Function.iterate_succ_apply' f k seed
          have hnk := htrace.index_injective n le_rfl k hk hn_eq_hk
          omega
    refine { outside := ?_, index_injective := ?_ }
    · intro i hi
      by_cases hin : i ≤ n
      · exact htrace.outside i hin
      · have hi_eq : i = n + 1 := by omega
        subst i
        exact ⟨hnext_ne_x, hnext_ne_c1, hnext_ne_c2, hnext_ne_c3⟩
    · intro i hi j hj hij
      by_cases hin : i ≤ n
      · by_cases hjn : j ≤ n
        · exact htrace.index_injective i hin j hjn hij
        · have hj_eq : j = n + 1 := by omega
          subst j
          exact False.elim (hnext_ne_prior i hin hij.symm)
      · have hi_eq : i = n + 1 := by omega
        subst i
        by_cases hjn : j ≤ n
        · exact False.elim (hnext_ne_prior j hjn hij)
        · omega

noncomputable def d4LeftFirstReturn_of_finite_leftInjective
    {α : Type u} [Finite α] [Magma' α]
    {x c1 c2 c3 seed : α} {n : Nat}
    (leftInjective : Function.Injective (fun z : α => x ◇ z))
    (hxc1 : x ◇ x = c1)
    (hc1c2 : x ◇ c1 = c2)
    (hc2c3 : x ◇ c2 = c3)
    (hc3x : x ◇ c3 = x)
    (htrace : D4LeftTrace x c1 c2 c3 seed n) :
    D4LeftFirstReturn x c1 c2 c3 seed n := by
  let f : α → α := fun z => x ◇ z
  let d : Nat := Function.minimalPeriod f seed
  have hf_injective : Function.Injective f := by
    simpa only [f] using leftInjective
  have hseed_periodic : seed ∈ Function.periodicPts f :=
    hf_injective.mem_periodicPts seed
  have hd_pos : 0 < d := by
    simpa only [d] using Function.minimalPeriod_pos_of_mem_periodicPts hseed_periodic
  have hreturns : (f^[d]) seed = seed := by
    simpa only [d] using (Function.iterate_minimalPeriod (f := f) (x := seed))
  have hn_lt_d : n < d := by
    by_contra hn_not_lt
    have hd_le_n : d ≤ n := Nat.le_of_not_gt hn_not_lt
    have hd_eq_zero : d = 0 := htrace.index_injective d hd_le_n 0 (Nat.zero_le n) (by
      change (f^[d]) seed = (f^[0]) seed
      simpa using hreturns)
    exact (Nat.ne_of_gt hd_pos) hd_eq_zero
  have htrace_until :
      ∀ m, n ≤ m → m < d → D4LeftTrace x c1 c2 c3 seed m := by
    intro m hnm
    induction m, hnm using Nat.le_induction with
    | base =>
        intro _
        exact htrace
    | succ k hnk ih =>
        intro hk_succ_lt_d
        have hk_lt_d : k < d := by omega
        have htrace_k : D4LeftTrace x c1 c2 c3 seed k := ih hk_lt_d
        rcases d4Trace_next_eq_seed_or_extend
            leftInjective hxc1 hc1c2 hc2c3 hc3x htrace_k with hreturn | hextend
        · have hk_succ_eq_zero : k + 1 = 0 := by
            apply Function.iterate_injOn_Iio_minimalPeriod
            · change k + 1 < d
              exact hk_succ_lt_d
            · change 0 < d
              exact hd_pos
            · simpa only [FirstReturn.orbitPoint, f,
                Function.iterate_zero_apply] using hreturn
          omega
        · exact hextend
  have hn_le_before : n ≤ d - 1 := Nat.le_sub_one_of_lt hn_lt_d
  have hbefore_lt_d : d - 1 < d := Nat.sub_one_lt (Nat.ne_of_gt hd_pos)
  have hsimple_prefix : D4LeftTrace x c1 c2 c3 seed (d - 1) :=
    htrace_until (d - 1) hn_le_before hbefore_lt_d
  refine ⟨d, hd_pos, ?_, hn_lt_d, ?_, hsimple_prefix⟩
  · simp only [d, f]
  · change (f^[d]) seed = seed
    exact hreturns

noncomputable def e677_firstReturnReduction {α : Type u} [Fintype α] [Magma' α]
    (h : E677 (α := α))
    {x c1 c2 c3 : α}
    (init : FiniteMagmaE677.FirstReturn.D4Initialization
      (Magma'.op (α := α)) x c1 c2 c3) :
    FiniteMagmaE677.FirstReturn.D4FirstReturnPacket
      (Magma'.op (α := α)) x c1 c2 c3 := by
  let p := init.distinguished
  have fr {seed : α} {n : ℕ}
      (trace : FiniteMagmaE677.FirstReturn.D4Trace
        (Magma'.op (α := α)) x c1 c2 c3 seed n) :
      FiniteMagmaE677.FirstReturn.D4FirstReturn
        (Magma'.op (α := α)) x c1 c2 c3 seed n :=
    d4LeftFirstReturn_of_finite_leftInjective
      (e677_leftMul_inj h x) p.orbit_c1 p.orbit_c2 p.orbit_c3 p.orbit_closes trace
  refine ⟨p, ?_⟩
  cases init.branch with
  | rSeedQThroughOne start fresh trace =>
      exact .rSeedQThroughOne start fresh trace (fr trace)
  | rSeedQThroughTwo start q_to_r fresh trace =>
      exact .rSeedQThroughTwo start q_to_r fresh trace (fr trace)
  | sSeedQThroughOne start fresh trace =>
      exact .sSeedQThroughOne start fresh trace (fr trace)
  | sSeedQThroughTwo start q_to_s fresh trace =>
      exact .sSeedQThroughTwo start q_to_s fresh trace (fr trace)
  | sSwapSeedT start q_to_s s_to_q fresh trace bridge =>
      exact .sSwapSeedT start q_to_s s_to_q fresh trace (fr trace) bridge

theorem periodic_cycles_phase_ne
    {β : Type u} {f : β → β} {a b : β} {m n i j : ℕ}
    (ha : Function.IsPeriodicPt f m a)
    (hb : Function.IsPeriodicPt f n b)
    (hm : 0 < m)
    (hj : j < n)
    (b_off_a : ∀ k, k < m → b ≠ (f^[k]) a) :
    (f^[i]) a ≠ (f^[j]) b := by
  intro phase_eq
  let k := (n - j + i) % m
  have hk_lt : k < m := Nat.mod_lt _ hm
  apply b_off_a k hk_lt
  have hroute : (f^[n - j + i]) a = b := by
    calc
      (f^[n - j + i]) a = (f^[n - j]) ((f^[i]) a) := by
        rw [Function.iterate_add_apply]
      _ = (f^[n - j]) ((f^[j]) b) := congrArg (f^[n - j]) phase_eq
      _ = (f^[n - j + j]) b := by rw [Function.iterate_add_apply]
      _ = (f^[n]) b := by rw [Nat.sub_add_cancel (Nat.le_of_lt hj)]
      _ = b := hb
  change b = (f^[k]) a
  rw [ha.iterate_mod_apply (n - j + i)]
  exact hroute.symm

end FiniteMagmaE677.SSwap
end

section
/-
Source-clean S-swap renewal proofs.  The assembler supplies imports and the
base aliases named in Definitions.fragment.lean.
-/

namespace FiniteMagmaE677.SSwap
local infixl:65 " ◇ " => Magma'.op

universe u
variable {α : Type u} [Magma' α]

private theorem q_collision_transport [Fintype α]
    (h : E677 α) {x c1 c2 c3 : α}
    (hcollision : c2 ◇ x = c3 ◇ x)
    (hpacket2 : c2 ◇ (c2 ◇ x) = c1) :
    (c3 ◇ (c2 ◇ x)) ◇ c3 = c1 ◇ c2 := by
  have hback2 :
      x = (c2 ◇ x) ◇ ((c2 ◇ (c2 ◇ x)) ◇ c2) := by
    exact e677_backward_recurrence h x c2
  have hback3 :
      x = (c3 ◇ x) ◇ ((c3 ◇ (c3 ◇ x)) ◇ c3) := by
    exact e677_backward_recurrence h x c3
  have hback2' : x = (c2 ◇ x) ◇ (c1 ◇ c2) := by
    simpa only [hpacket2] using hback2
  have hback3' :
      x = (c2 ◇ x) ◇ ((c3 ◇ (c2 ◇ x)) ◇ c3) := by
    simpa only [← hcollision] using hback3
  exact (e677_left_cancel h (c2 ◇ x) (hback2'.symm.trans hback3')).symm

private theorem star_eq_of_rightCollision [Fintype α]
    (h : E677 α) (z : α) {a b : α}
    (hab : a ◇ z = b ◇ z) :
    (a ◇ (a ◇ z)) ◇ a = (b ◇ (b ◇ z)) ◇ b := by
  apply e677_left_cancel h (a ◇ z)
  calc
    (a ◇ z) ◇ ((a ◇ (a ◇ z)) ◇ a) = z :=
      (e677_backward_recurrence h z a).symm
    _ = (b ◇ z) ◇ ((b ◇ (b ◇ z)) ◇ b) :=
      e677_backward_recurrence h z b
    _ = (a ◇ z) ◇ ((b ◇ (b ◇ z)) ◇ b) := by rw [hab]

set_option linter.unusedFintypeInType false in
theorem e677_d4_s_swap_t_mul_c3_ne_t [Fintype α]
    (h : E677 α)
    {x c1 c2 c3 t : α}
    (hx1 : x ◇ x = c1) (hx2 : x ◇ c1 = c2)
    (hx3 : x ◇ c2 = c3) (hx4 : x ◇ c3 = x)
    (ht2 : t ◇ c2 = c3)
    (hstar : (t ◇ c3) ◇ t = c1)
    (ht_ne_x : t ≠ x) :
    t ◇ c3 ≠ t := by
  intro ht3
  have htt : t ◇ t = c1 := by
    simpa only [ht3] using hstar
  have hx_c1x : x ◇ (c1 ◇ x) = c3 := by
    apply e677_left_cancel h x
    calc
      x ◇ (x ◇ (c1 ◇ x)) = x := by
        simpa only [hx1] using (h x x).symm
      _ = x ◇ c3 := hx4.symm
  have hc1x : c1 ◇ x = c2 := by
    apply e677_left_cancel h x
    exact hx_c1x.trans hx3.symm
  have ht_c1t : t ◇ (c1 ◇ t) = c3 := by
    apply e677_left_cancel h t
    calc
      t ◇ (t ◇ (c1 ◇ t)) = t := by
        simpa only [htt] using (h t t).symm
      _ = t ◇ c3 := ht3.symm
  have hc1t : c1 ◇ t = c2 := by
    apply e677_left_cancel h t
    exact ht_c1t.trans ht2.symm
  have hxt : x = t := by
    apply e677_left_cancel h c1
    exact hc1x.trans hc1t.symm
  exact ht_ne_x hxt.symm

set_option linter.unusedFintypeInType false in
theorem e677_d4_s_swap_crossCycleReduction [Fintype α]
    (h : E677 α)
    {x c1 c2 c3 : α}
    (packet : E677D4QDistinguishedPacket x c1 c2 c3)
    (start : E677D4QSTaggedTraceStart x c1 c2 c3)
    (q_to_s : x ◇ (c2 ◇ x) = c3 ◇ (c2 ◇ x))
    (s_to_q : x ◇ (c3 ◇ (c2 ◇ x)) = c2 ◇ x)
    (fresh : E677FreshOutsideSix x c1 c2 c3
      (c2 ◇ x) (c3 ◇ (c2 ◇ x)) (c2 ◇ (c3 ◇ (c2 ◇ x))))
    (first : D4LeftFirstReturn x c1 c2 c3
      (c2 ◇ (c3 ◇ (c2 ◇ x))) 0)
    (bridge : (c2 ◇ (c3 ◇ (c2 ◇ x))) ◇ c2 = c3)
    (star : ((c2 ◇ (c3 ◇ (c2 ◇ x))) ◇ c3) ◇
      (c2 ◇ (c3 ◇ (c2 ◇ x))) = c1) :
    D4SSwapCrossCycleReduction x c1 c2 c3
      (c2 ◇ x) (c3 ◇ (c2 ◇ x))
      (c2 ◇ (c3 ◇ (c2 ◇ x))) first := by
  let q := c2 ◇ x
  let s := c3 ◇ q
  let t := c2 ◇ s
  let u := t ◇ c3
  change x ◇ q = s at q_to_s
  change x ◇ s = q at s_to_q
  change E677FreshOutsideSix x c1 c2 c3 q s t at fresh
  change D4LeftFirstReturn x c1 c2 c3 t 0 at first
  change t ◇ c2 = c3 at bridge
  change u ◇ t = c1 at star
  change D4SSwapCrossCycleReduction x c1 c2 c3 q s t first
  have hu_ne_t : u ≠ t := by
    simpa only [u] using e677_d4_s_swap_t_mul_c3_ne_t h
      packet.orbit_c1 packet.orbit_c2 packet.orbit_c3 packet.orbit_closes
      bridge star fresh.1
  have hs_c3 : s ◇ c3 = c1 := by
    exact (q_collision_transport h packet.q_collision
      packet.q_packet_return).trans start.r_eq_c1
  have hq_return : c2 ◇ q = c1 := packet.q_packet_return
  have hr_eq_c1 : c1 ◇ c2 = c1 := start.r_eq_c1
  by_cases hu_q : u = q
  · have hq_t : q ◇ t = c1 := by
      rw [← hu_q]
      exact star
    have hq_c1 : q ◇ c1 = x := by
      apply e677_left_cancel h c2
      calc
        c2 ◇ (q ◇ c1) = q := by
          simpa only [hq_return, hr_eq_c1] using (h q c2).symm
        _ = c2 ◇ x := by rfl
    have hc1_s : c1 ◇ s = t := by
      apply e677_left_cancel h q
      calc
        q ◇ (c1 ◇ s) = c1 := by
          simpa only [hq_c1, q_to_s] using (h c1 q).symm
        _ = q ◇ t := hq_t.symm
    exact .dual {
      t_c3_eq_q := by simpa only [u] using hu_q
      q_t_eq_c1 := hq_t
      c1_s_eq_t := hc1_s
      c2_s_eq_t := by rfl
    }
  · by_cases hu_phase : ∃ k, k < first.period ∧ u = LxPhase x t k
    · rcases hu_phase with ⟨k, hk_lt, hu_eq⟩
      have hk_pos : 0 < k := by
        have hk_ne : k ≠ 0 := by
          intro hk_zero
          subst k
          apply hu_ne_t
          simpa only [LxPhase, Function.iterate_zero_apply] using hu_eq
        omega
      exact .positivePhase {
        phase := k
        phase_pos := hk_pos
        phase_lt := hk_lt
        t_c3_eq_phase := by simpa only [u] using hu_eq
        phase_t_eq_c1 := by
          rw [← hu_eq]
          exact star
      }
    · have hu_x : u ≠ x := by
        intro hu_eq_x
        apply fresh.1
        apply e677_left_cancel h x
        calc
          x ◇ t = u ◇ t := by rw [hu_eq_x]
          _ = c1 := star
          _ = x ◇ x := packet.orbit_c1.symm
      have hu_c1 : u ≠ c1 := by
        intro hu_eq_c1
        apply fresh.2.2.1
        apply e677_left_cancel h c1
        calc
          c1 ◇ t = u ◇ t := by rw [hu_eq_c1]
          _ = c1 := star
          _ = c1 ◇ c2 := start.r_eq_c1.symm
      have hu_c2 : u ≠ c2 := by
        intro hu_eq_c2
        apply fresh.2.2.2.2.1
        apply e677_left_cancel h c2
        calc
          c2 ◇ t = u ◇ t := by rw [hu_eq_c2]
          _ = c1 := star
          _ = c2 ◇ q := packet.q_packet_return.symm
      have hu_c3 : u ≠ c3 := by
        intro hu_eq_c3
        have ht_c3 : t ◇ c3 = c3 := by
          simpa only [u] using hu_eq_c3
        have hc3_c2 : c3 = c2 := by
          apply e677_left_cancel h t
          exact ht_c3.trans bridge.symm
        exact packet.c2_ne_c3 hc3_c2.symm
      have hu_s : u ≠ s := by
        intro hu_eq_s
        apply fresh.2.2.2.1
        apply e677_left_cancel h s
        calc
          s ◇ t = u ◇ t := by rw [hu_eq_s]
          _ = c1 := star
          _ = s ◇ c3 := hs_c3.symm
      have hu_fresh : E677FreshOutsideSix x c1 c2 c3 q s u :=
        ⟨hu_x, hu_c1, hu_c2, hu_c3, hu_q, hu_s⟩
      have hu_trace : D4LeftTrace x c1 c2 c3 u 0 := by
        refine ⟨?_, ?_⟩
        · intro i hi
          have hi_zero : i = 0 := by omega
          subst i
          simpa only [Function.iterate_zero_apply] using
            ⟨hu_x, hu_c1, hu_c2, hu_c3⟩
        · intro i hi j hj _
          omega
      have hu_first : D4LeftFirstReturn x c1 c2 c3 u 0 :=
        d4LeftFirstReturn_of_finite_leftInjective
          (e677_leftMul_inj h x)
          packet.orbit_c1 packet.orbit_c2 packet.orbit_c3 packet.orbit_closes
          hu_trace
      exact .newCycle {
        u := u
        u_eq := rfl
        fresh := hu_fresh
        off_t_cycle := by
          intro k hk hu_eq
          exact hu_phase ⟨k, hk, hu_eq⟩
        firstReturn := hu_first
        u_t_eq_c1 := star
      }


theorem e677_d4_s_swap_q_s_right_c2_collision [Fintype α]
    (h : E677 α)
    {x c1 c2 c3 : α}
    (packet : E677D4QDistinguishedPacket x c1 c2 c3)
    (start : E677D4QSTaggedTraceStart x c1 c2 c3)
    (bridge : (c2 ◇ (c3 ◇ (c2 ◇ x))) ◇ c2 = c3) :
    (c2 ◇ x) ◇ c2 = (c3 ◇ (c2 ◇ x)) ◇ c2 := by
  let q := c2 ◇ x
  let s := c3 ◇ q
  let t := c2 ◇ s
  change t ◇ c2 = c3 at bridge
  change q ◇ c2 = s ◇ c2
  have hc2_s : c2 ◇ s = t := rfl
  have hq_return : c2 ◇ q = c1 := packet.q_packet_return
  have hc1_q : c1 ◇ q = x := packet.q_packet_preimage
  have hx_c1 : x ◇ c1 = c2 := packet.orbit_c2
  have hs_c3 : s ◇ c3 = c1 := by
    exact (q_collision_transport h packet.q_collision
      packet.q_packet_return).trans start.r_eq_c1
  have hc2_c1 : c2 ◇ c1 = s := by
    simpa only [hc2_s, bridge, hs_c3] using (h s c2).symm
  have hc1_qc2 : c1 ◇ (q ◇ c2) = q := by
    simpa only [hc1_q, hx_c1] using (h q c1).symm
  have hc1_sc2 : c1 ◇ (s ◇ c2) = q := by
    apply e677_left_cancel h c2
    calc
      c2 ◇ (c1 ◇ (s ◇ c2)) = c1 := by
        simpa only [hc2_c1] using (h c1 c2).symm
      _ = c2 ◇ q := hq_return.symm
  exact e677_left_cancel h c1 (hc1_qc2.trans hc1_sc2.symm)

set_option linter.unusedFintypeInType false in
theorem e677_d4_s_swap_explicitQFixer [Fintype α]
    (h : E677 α)
    {x c1 c2 c3 : α}
    (packet : E677D4QDistinguishedPacket x c1 c2 c3)
    (start : E677D4QSTaggedTraceStart x c1 c2 c3) :
    ((c2 ◇ x) ◇ ((c2 ◇ x) ◇ x)) ◇ (c2 ◇ x) = c2 ◇ x := by
  let q := c2 ◇ x
  let a := q ◇ x
  change (q ◇ a) ◇ q = q
  have hq_return : c2 ◇ q = c1 := packet.q_packet_return
  have hq_c1 : q ◇ c1 = x := by
    apply e677_left_cancel h c2
    calc
      c2 ◇ (q ◇ c1) = q := by
        simpa only [hq_return, start.r_eq_c1] using (h q c2).symm
      _ = c2 ◇ x := by rfl
  have hx_aq : x ◇ (a ◇ q) = c1 := by
    apply e677_left_cancel h q
    calc
      q ◇ (x ◇ (a ◇ q)) = x := by
        simpa only [a] using (h x q).symm
      _ = q ◇ c1 := hq_c1.symm
  have ha_q : a ◇ q = x := by
    apply e677_left_cancel h x
    exact hx_aq.trans packet.orbit_c1.symm
  apply e677_left_cancel h a
  calc
    a ◇ ((q ◇ a) ◇ q) = x :=
      (e677_backward_recurrence h x q).symm
    _ = a ◇ q := ha_q.symm

set_option linter.unusedFintypeInType false in
theorem e677_d4_s_swap_commonRenewalPacket [Fintype α]
    (h : E677 α)
    {x c1 c2 c3 : α}
    (packet : E677D4QDistinguishedPacket x c1 c2 c3)
    (start : E677D4QSTaggedTraceStart x c1 c2 c3)
    (q_to_s : x ◇ (c2 ◇ x) = c3 ◇ (c2 ◇ x))
    (s_to_q : x ◇ (c3 ◇ (c2 ◇ x)) = c2 ◇ x)
    (bridge : (c2 ◇ (c3 ◇ (c2 ◇ x))) ◇ c2 = c3) :
    D4SSwapCommonRenewalPacket x c1 c2 c3
      (c2 ◇ x) (c3 ◇ (c2 ◇ x)) := by
  let q := c2 ◇ x
  let s := c3 ◇ q
  let a := q ◇ x
  let p := q ◇ a
  change x ◇ q = s at q_to_s
  change x ◇ s = q at s_to_q
  change D4SSwapCommonRenewalPacket x c1 c2 c3 q s
  have hp_q : p ◇ q = q := by
    simpa only [p, a, q] using e677_d4_s_swap_explicitQFixer h packet start
  have hq_return : c2 ◇ q = c1 := packet.q_packet_return
  have hq_c1 : q ◇ c1 = x := by
    apply e677_left_cancel h c2
    calc
      c2 ◇ (q ◇ c1) = q := by
        simpa only [hq_return, start.r_eq_c1] using (h q c2).symm
      _ = c2 ◇ x := by rfl
  have hp_x : p ≠ x := by
    intro hp
    have : q = s := hp_q.symm.trans (by simpa only [hp] using q_to_s)
    exact start.s_ne_q this.symm
  have hp_c1 : p ≠ c1 := by
    intro hp
    have : q = x := hp_q.symm.trans (by
      simpa only [hp] using packet.q_packet_preimage)
    exact packet.q_ne_x this
  have hp_c2 : p ≠ c2 := by
    intro hp
    have : q = c1 := hp_q.symm.trans (by
      simpa only [hp] using packet.q_packet_return)
    exact packet.q_ne_c1 this
  have hp_c3 : p ≠ c3 := by
    intro hp
    have : q = s := hp_q.symm.trans (by simpa only [hp, s])
    exact start.s_ne_q this.symm
  have hp_ne_q : p ≠ q := by
    intro hp
    have ha_eq_q : a = q := e677_left_cancel h q (by
      calc
        q ◇ a = p := rfl
        _ = q := hp
        _ = q ◇ q := by simpa only [hp] using hp_q.symm)
    have : x = q := e677_left_cancel h q (by
      calc
        q ◇ x = a := rfl
        _ = q := ha_eq_q
        _ = q ◇ q := by simpa only [hp] using hp_q.symm)
    exact packet.q_ne_x this.symm
  have hp_s : p ≠ s := by
    intro hp
    have hs_q : s ◇ q = q := by simpa only [hp] using hp_q
    have hs_a : s ◇ a = q := by
      apply e677_left_cancel h x
      calc
        x ◇ (s ◇ a) = s := by
          simpa only [s_to_q, a] using (h s x).symm
        _ = x ◇ q := q_to_s.symm
    have ha_eq_q : a = q := e677_left_cancel h s (hs_a.trans hs_q.symm)
    have ha_eq_qqs : a = q ◇ (q ◇ s) := by
      apply e677_left_cancel h s
      calc
        s ◇ a = q := hs_a
        _ = s ◇ (q ◇ (q ◇ s)) := by
          simpa only [hs_q] using h q s
    have hx_eq_qs : x = q ◇ s := e677_left_cancel h q (by
      simpa only [a] using ha_eq_qqs)
    have : s = c1 := e677_left_cancel h q (by
      calc
        q ◇ s = x := hx_eq_qs.symm
        _ = q ◇ c1 := hq_c1.symm)
    exact start.s_ne_c1 this
  refine {
    q_s_right_c2_collision := ?_
    qFixer_fixes_q := hp_q
    qFixer_fresh := ⟨hp_x, hp_c1, hp_c2, hp_c3, hp_ne_q, hp_s⟩
  }
  simpa only [q, s] using
    e677_d4_s_swap_q_s_right_c2_collision h packet start bridge

theorem e677_d4_s_swap_cycleRenewalPacket [Fintype α]
    (h : E677 α)
    {x c1 c2 c3 : α}
    (packet : E677D4QDistinguishedPacket x c1 c2 c3)
    (start : E677D4QSTaggedTraceStart x c1 c2 c3)
    (q_to_s : x ◇ (c2 ◇ x) = c3 ◇ (c2 ◇ x))
    (s_to_q : x ◇ (c3 ◇ (c2 ◇ x)) = c2 ◇ x)
    (fresh : E677FreshOutsideSix x c1 c2 c3
      (c2 ◇ x) (c3 ◇ (c2 ◇ x)) (c2 ◇ (c3 ◇ (c2 ◇ x))))
    (initial_trace : D4LeftTrace x c1 c2 c3
      (c2 ◇ (c3 ◇ (c2 ◇ x))) 0)
    (first : D4LeftFirstReturn x c1 c2 c3
      (c2 ◇ (c3 ◇ (c2 ◇ x))) 0)
    (bridge : (c2 ◇ (c3 ◇ (c2 ◇ x))) ◇ c2 = c3)
    (star : ((c2 ◇ (c3 ◇ (c2 ◇ x))) ◇ c3) ◇
      (c2 ◇ (c3 ◇ (c2 ◇ x))) = c1) :
    D4SSwapCycleRenewalPacket x c1 c2 c3
      (c2 ◇ x) (c3 ◇ (c2 ◇ x))
      (c2 ◇ (c3 ◇ (c2 ◇ x))) first := by
  exact {
    basePacket := packet
    traceStart := start
    q_to_s := q_to_s
    s_to_q := s_to_q
    t_fresh := fresh
    initial_trace := initial_trace
    bridge := bridge
    star := star
    common := e677_d4_s_swap_commonRenewalPacket h packet start q_to_s s_to_q bridge
    reduction := e677_d4_s_swap_crossCycleReduction h packet start q_to_s s_to_q
      fresh first bridge star
  }

/-- Adapter from the published explicit-operation S-swap payload.  The
published branch carries `bridge` but not the normalized Star equation; the
equation is derived internally from E677 and the right-collision recurrence. -/
theorem e677_d4_s_swap_cycleRenewalPacket_of_published [Fintype α]
    (h : E677 α)
    {x c1 c2 c3 : α}
    (packet : E677D4QDistinguishedPacket x c1 c2 c3)
    (start : E677D4QSTaggedTraceStart x c1 c2 c3)
    (q_to_s : x ◇ (c2 ◇ x) = c3 ◇ (c2 ◇ x))
    (s_to_q : x ◇ (c3 ◇ (c2 ◇ x)) = c2 ◇ x)
    (fresh : E677FreshOutsideSix x c1 c2 c3
      (c2 ◇ x) (c3 ◇ (c2 ◇ x)) (c2 ◇ (c3 ◇ (c2 ◇ x))))
    (initial_trace : D4LeftTrace x c1 c2 c3
      (c2 ◇ (c3 ◇ (c2 ◇ x))) 0)
    (first : D4LeftFirstReturn x c1 c2 c3
      (c2 ◇ (c3 ◇ (c2 ◇ x))) 0)
    (bridge : (c2 ◇ (c3 ◇ (c2 ◇ x))) ◇ c2 = c3) :
    D4SSwapCycleRenewalPacket x c1 c2 c3
      (c2 ◇ x) (c3 ◇ (c2 ◇ x))
      (c2 ◇ (c3 ◇ (c2 ◇ x))) first := by
  let t := c2 ◇ (c3 ◇ (c2 ◇ x))
  have hcollision : t ◇ c2 = x ◇ c2 := by
    simpa only [t] using bridge.trans packet.orbit_c3.symm
  have hstar := star_eq_of_rightCollision h c2 hcollision
  have hnormalized : (t ◇ c3) ◇ t = c1 := by
    calc
      (t ◇ c3) ◇ t = (t ◇ (t ◇ c2)) ◇ t := by rw [bridge]
      _ = (x ◇ (x ◇ c2)) ◇ x := hstar
      _ = (x ◇ c3) ◇ x := by rw [packet.orbit_c3]
      _ = x ◇ x := by rw [packet.orbit_closes]
      _ = c1 := packet.orbit_c1
  exact e677_d4_s_swap_cycleRenewalPacket h packet start q_to_s s_to_q
    fresh initial_trace first bridge hnormalized

set_option linter.unusedFintypeInType false in
theorem e677_d4_s_swap_qFixerCycleTransition [Fintype α]
    (h : E677 α)
    {x c1 c2 c3 q s t : α}
    {first : D4LeftFirstReturn x c1 c2 c3 t 0}
    (input : D4SSwapCycleRenewalPacket x c1 c2 c3 q s t first) :
    D4SSwapQFixerCycleTransition x c1 c2 c3 q t
      (q ◇ (q ◇ x)) first := by
  classical
  let p := q ◇ (q ◇ x)
  change D4SSwapQFixerCycleTransition x c1 c2 c3 q t p first
  by_cases contact : ∃ k, k < first.period ∧ p = LxPhase x t k
  · rcases contact with ⟨k, hk_lt, hp_eq⟩
    exact .knownCycle k hk_lt hp_eq (by
      rw [← hp_eq]
      exact input.common.qFixer_fixes_q)
  · have p_trace : D4LeftTrace x c1 c2 c3 p 0 := by
      refine ⟨?_, ?_⟩
      · intro i hi
        have hi_zero : i = 0 := by omega
        subst i
        simpa only [Function.iterate_zero_apply] using
          ⟨input.common.qFixer_fresh.1,
            input.common.qFixer_fresh.2.1,
            input.common.qFixer_fresh.2.2.1,
            input.common.qFixer_fresh.2.2.2.1⟩
      · intro i hi j hj _
        omega
    have p_first : D4LeftFirstReturn x c1 c2 c3 p 0 :=
      d4LeftFirstReturn_of_finite_leftInjective
        (e677_leftMul_inj h x)
        input.basePacket.orbit_c1 input.basePacket.orbit_c2
        input.basePacket.orbit_c3 input.basePacket.orbit_closes p_trace
    exact .strictGrowth (by
      intro k hk_lt hp_eq
      exact contact ⟨k, hk_lt, hp_eq⟩) p_first input.common.qFixer_fixes_q

end FiniteMagmaE677.SSwap
end

namespace FiniteMagmaE677.SSwap
local infixl:65 " ◇ " => Magma'.op
section
universe u
variable {α : Type u} [Magma' α] [DecidableEq α]

/-- A first-return packet makes its canonical finite cycle have exactly its
recorded period many elements. -/
theorem card_lxCycleFinset_of_firstReturn
    {x c1 c2 c3 seed : α} {n : ℕ}
    (first : D4LeftFirstReturn x c1 c2 c3 seed n) :
    (lxCycleFinset x seed first.period).card = first.period := by
  unfold lxCycleFinset
  calc
    ((Finset.range first.period).image (LxPhase x seed)).card =
        (Finset.range first.period).card := by
      apply Finset.card_image_of_injOn
      intro i hi j hj hij
      rw [Finset.mem_coe, Finset.mem_range] at hi hj
      exact first.simple_prefix.index_injective i
        (Nat.le_sub_one_of_lt hi) j (Nat.le_sub_one_of_lt hj) hij
    _ = first.period := Finset.card_range first.period

private theorem accounting_periodic_cycles_phase_ne
    {β : Type*} {f : β → β} {a b : β} {m n i j : ℕ}
    (ha : Function.IsPeriodicPt f m a)
    (hb : Function.IsPeriodicPt f n b)
    (hm : 0 < m)
    (hj : j < n)
    (b_off_a : ∀ k, k < m → b ≠ (f^[k]) a) :
    (f^[i]) a ≠ (f^[j]) b := by
  intro phase_eq
  let k := (n - j + i) % m
  have hk_lt : k < m := Nat.mod_lt _ hm
  apply b_off_a k hk_lt
  have hroute : (f^[n - j + i]) a = b := by
    calc
      (f^[n - j + i]) a = (f^[n - j]) ((f^[i]) a) := by
        rw [Function.iterate_add_apply]
      _ = (f^[n - j]) ((f^[j]) b) := congrArg (f^[n - j]) phase_eq
      _ = (f^[n - j + j]) b := by rw [Function.iterate_add_apply]
      _ = (f^[n]) b := by rw [Nat.sub_add_cancel (Nat.le_of_lt hj)]
      _ = b := hb
  change b = (f^[k]) a
  rw [ha.iterate_mod_apply (n - j + i)]
  exact hroute.symm

omit [DecidableEq α] in
private theorem d4SSwap_q_fresh_from_base
    {x c1 c2 c3 q s t : α}
    {first : D4LeftFirstReturn x c1 c2 c3 t 0}
    (input : D4SSwapCycleRenewalPacket x c1 c2 c3 q s t first) :
    q ≠ x ∧ q ≠ c1 ∧ q ≠ c2 ∧ q ≠ c3 := by
  have hq_x : q ≠ x := by
    intro hq
    have hs : s = c1 := by
      calc
        s = x ◇ q := input.q_to_s.symm
        _ = x ◇ x := by rw [hq]
        _ = c1 := input.basePacket.orbit_c1
    have hq_c2 : q = c2 := by
      calc
        q = x ◇ s := input.s_to_q.symm
        _ = x ◇ c1 := by rw [hs]
        _ = c2 := input.basePacket.orbit_c2
    exact input.basePacket.x_ne_c2 (hq.symm.trans hq_c2)
  have hq_c1 : q ≠ c1 := by
    intro hq
    have hs : s = c2 := by
      calc
        s = x ◇ q := input.q_to_s.symm
        _ = x ◇ c1 := by rw [hq]
        _ = c2 := input.basePacket.orbit_c2
    have hq_c3 : q = c3 := by
      calc
        q = x ◇ s := input.s_to_q.symm
        _ = x ◇ c2 := by rw [hs]
        _ = c3 := input.basePacket.orbit_c3
    exact input.basePacket.c1_ne_c3 (hq.symm.trans hq_c3)
  have hq_c2 : q ≠ c2 := by
    intro hq
    have hs : s = c3 := by
      calc
        s = x ◇ q := input.q_to_s.symm
        _ = x ◇ c2 := by rw [hq]
        _ = c3 := input.basePacket.orbit_c3
    have hq_x' : q = x := by
      calc
        q = x ◇ s := input.s_to_q.symm
        _ = x ◇ c3 := by rw [hs]
        _ = x := input.basePacket.orbit_closes
    exact input.basePacket.x_ne_c2 (hq_x'.symm.trans hq)
  have hq_c3 : q ≠ c3 := by
    intro hq
    have hs : s = x := by
      calc
        s = x ◇ q := input.q_to_s.symm
        _ = x ◇ c3 := by rw [hq]
        _ = x := input.basePacket.orbit_closes
    have hq_c1' : q = c1 := by
      calc
        q = x ◇ s := input.s_to_q.symm
        _ = x ◇ x := by rw [hs]
        _ = c1 := input.basePacket.orbit_c1
    exact input.basePacket.c1_ne_c3 (hq_c1'.symm.trans hq)
  exact ⟨hq_x, hq_c1, hq_c2, hq_c3⟩

omit [DecidableEq α] in
private theorem d4SSwap_s_fresh_from_base
    {x c1 c2 c3 q s t : α}
    {first : D4LeftFirstReturn x c1 c2 c3 t 0}
    (input : D4SSwapCycleRenewalPacket x c1 c2 c3 q s t first) :
    s ≠ x ∧ s ≠ c1 ∧ s ≠ c2 ∧ s ≠ c3 := by
  rcases d4SSwap_q_fresh_from_base input with ⟨hq_x, hq_c1, hq_c2, hq_c3⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hs
    apply hq_c1
    calc
      q = x ◇ s := input.s_to_q.symm
      _ = x ◇ x := by rw [hs]
      _ = c1 := input.basePacket.orbit_c1
  · intro hs
    apply hq_c2
    calc
      q = x ◇ s := input.s_to_q.symm
      _ = x ◇ c1 := by rw [hs]
      _ = c2 := input.basePacket.orbit_c2
  · intro hs
    apply hq_c3
    calc
      q = x ◇ s := input.s_to_q.symm
      _ = x ◇ c2 := by rw [hs]
      _ = c3 := input.basePacket.orbit_c3
  · intro hs
    apply hq_x
    calc
      q = x ◇ s := input.s_to_q.symm
      _ = x ◇ c3 := by rw [hs]
      _ = x := input.basePacket.orbit_closes

/-- The six named points have cardinality six when the packet's two marked
points are explicitly distinct. -/
theorem d4SSwapSixFinset_card_of_q_ne_s
    {x c1 c2 c3 q s t : α}
    {first : D4LeftFirstReturn x c1 c2 c3 t 0}
    (input : D4SSwapCycleRenewalPacket x c1 c2 c3 q s t first)
    (q_ne_s : q ≠ s) :
    (d4SSwapSixFinset x c1 c2 c3 q s).card = 6 := by
  rcases d4SSwap_q_fresh_from_base input with ⟨hq_x, hq_c1, hq_c2, hq_c3⟩
  rcases d4SSwap_s_fresh_from_base input with ⟨hs_x, hs_c1, hs_c2, hs_c3⟩
  have hx : x ∉ ({c1, c2, c3, q, s} : Finset α) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨input.basePacket.x_ne_c1, input.basePacket.x_ne_c2,
      input.basePacket.x_ne_c3, hq_x.symm, hs_x.symm⟩
  have hc1 : c1 ∉ ({c2, c3, q, s} : Finset α) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨input.basePacket.c1_ne_c2, input.basePacket.c1_ne_c3,
      hq_c1.symm, hs_c1.symm⟩
  have hc2 : c2 ∉ ({c3, q, s} : Finset α) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨input.basePacket.c2_ne_c3, hq_c2.symm, hs_c2.symm⟩
  have hc3 : c3 ∉ ({q, s} : Finset α) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hq_c3.symm, hs_c3.symm⟩
  have hq : q ∉ ({s} : Finset α) := by
    simpa only [Finset.mem_singleton] using q_ne_s
  unfold d4SSwapSixFinset
  rw [Finset.card_insert_of_notMem hx, Finset.card_insert_of_notMem hc1,
    Finset.card_insert_of_notMem hc2, Finset.card_insert_of_notMem hc3,
    Finset.card_insert_of_notMem hq, Finset.card_singleton]

private theorem d4SSwapSixFinset_card_lower_bound
    {x c1 c2 c3 q s t : α}
    {first : D4LeftFirstReturn x c1 c2 c3 t 0}
    (input : D4SSwapCycleRenewalPacket x c1 c2 c3 q s t first) :
    5 ≤ (d4SSwapSixFinset x c1 c2 c3 q s).card := by
  rcases d4SSwap_q_fresh_from_base input with ⟨hq_x, hq_c1, hq_c2, hq_c3⟩
  have hx : x ∉ ({c1, c2, c3, q} : Finset α) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨input.basePacket.x_ne_c1, input.basePacket.x_ne_c2,
      input.basePacket.x_ne_c3, hq_x.symm⟩
  have hc1 : c1 ∉ ({c2, c3, q} : Finset α) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨input.basePacket.c1_ne_c2, input.basePacket.c1_ne_c3, hq_c1.symm⟩
  have hc2 : c2 ∉ ({c3, q} : Finset α) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨input.basePacket.c2_ne_c3, hq_c2.symm⟩
  have hc3 : c3 ∉ ({q} : Finset α) := by
    simpa only [Finset.mem_singleton] using hq_c3.symm
  have hcard_five : ({x, c1, c2, c3, q} : Finset α).card = 5 := by
    rw [Finset.card_insert_of_notMem hx, Finset.card_insert_of_notMem hc1,
      Finset.card_insert_of_notMem hc2, Finset.card_insert_of_notMem hc3,
      Finset.card_singleton]
  have hsubset : ({x, c1, c2, c3, q} : Finset α) ⊆
      d4SSwapSixFinset x c1 c2 c3 q s := by
    unfold d4SSwapSixFinset
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
    aesop
  calc
    5 = ({x, c1, c2, c3, q} : Finset α).card := hcard_five.symm
    _ ≤ (d4SSwapSixFinset x c1 c2 c3 q s).card :=
      Finset.card_le_card hsubset

/-- A fresh first-return seed has its entire finite cycle disjoint from the six
named S-swap points. -/
theorem d4SSwapSixFinset_disjoint_lxCycleFinset
    {x c1 c2 c3 q s seed t : α}
    {first : D4LeftFirstReturn x c1 c2 c3 t 0}
    (input : D4SSwapCycleRenewalPacket x c1 c2 c3 q s t first)
    (seedFresh : E677FreshOutsideSix x c1 c2 c3 q s seed)
    (seedFirst : D4LeftFirstReturn x c1 c2 c3 seed 0) :
    Disjoint (d4SSwapSixFinset x c1 c2 c3 q s)
      (lxCycleFinset x seed seedFirst.period) := by
  let f : α → α := fun z ↦ x ◇ z
  have hq_periodic : Function.IsPeriodicPt f 2 q := by
    change x ◇ (x ◇ q) = q
    rw [input.q_to_s, input.s_to_q]
  have hseed_periodic : Function.IsPeriodicPt f seedFirst.period seed := by
    exact seedFirst.returns
  have seed_off_q_cycle : ∀ k, k < 2 → seed ≠ (f^[k]) q := by
    intro k hk
    interval_cases k
    · simpa only [Function.iterate_zero_apply] using seedFresh.2.2.2.2.1
    · change seed ≠ x ◇ q
      rw [input.q_to_s]
      exact seedFresh.2.2.2.2.2
  rw [Finset.disjoint_left]
  intro z hz_named hz_cycle
  have hz_cases :
      z = x ∨ z = c1 ∨ z = c2 ∨ z = c3 ∨ z = q ∨ z = s := by
    simpa only [d4SSwapSixFinset, Finset.mem_insert, Finset.mem_singleton]
      using hz_named
  rcases Finset.mem_image.mp hz_cycle with ⟨k, hk, hk_eq⟩
  simp only [Finset.mem_range] at hk
  have hk_before : k ≤ seedFirst.period - 1 := Nat.le_sub_one_of_lt hk
  rcases hz_cases with hz_x | hz_c1 | hz_c2 | hz_c3 | hz_q | hz_s
  · exact (seedFirst.simple_prefix.outside k hk_before).1 (hk_eq.trans hz_x)
  · exact (seedFirst.simple_prefix.outside k hk_before).2.1 (hk_eq.trans hz_c1)
  · exact (seedFirst.simple_prefix.outside k hk_before).2.2.1 (hk_eq.trans hz_c2)
  · exact (seedFirst.simple_prefix.outside k hk_before).2.2.2 (hk_eq.trans hz_c3)
  · apply accounting_periodic_cycles_phase_ne hq_periodic hseed_periodic (by omega)
      (i := 0) (j := k) hk seed_off_q_cycle
    simpa only [Function.iterate_zero_apply, LxPhase, f] using
      (hk_eq.trans hz_q).symm
  · apply accounting_periodic_cycles_phase_ne hq_periodic hseed_periodic (by omega)
      (i := 1) (j := k) hk seed_off_q_cycle
    have hq_s : (f^[1]) q = s := by
      change x ◇ q = s
      exact input.q_to_s
    simpa only [LxPhase, f] using hq_s.trans (hk_eq.trans hz_s).symm

/-- Two finite first-return cycles are disjoint when the second seed is off the
first cycle. -/
theorem lxCycleFinset_disjoint_of_off_cycle
    {x c1 c2 c3 a b : α}
    (aFirst : D4LeftFirstReturn x c1 c2 c3 a 0)
    (bFirst : D4LeftFirstReturn x c1 c2 c3 b 0)
    (b_off_a : ∀ k, k < aFirst.period → b ≠ LxPhase x a k) :
    Disjoint (lxCycleFinset x a aFirst.period)
      (lxCycleFinset x b bFirst.period) := by
  let f : α → α := fun z ↦ x ◇ z
  have ha_periodic : Function.IsPeriodicPt f aFirst.period a := aFirst.returns
  have hb_periodic : Function.IsPeriodicPt f bFirst.period b := bFirst.returns
  rw [Finset.disjoint_left]
  intro z hz_a hz_b
  rcases Finset.mem_image.mp hz_a with ⟨i, hi, hi_eq⟩
  rcases Finset.mem_image.mp hz_b with ⟨j, hj, hj_eq⟩
  simp only [Finset.mem_range] at hi hj
  apply accounting_periodic_cycles_phase_ne ha_periodic hb_periodic aFirst.period_pos
    hj b_off_a
  simpa only [LxPhase] using hi_eq.trans hj_eq.symm

/-- In the fresh-cycle leaf, the six named points, the old `t`-cycle, and the
new `u`-cycle are pairwise disjoint. -/
theorem d4SSwapNewCycle_pairwiseDisjoint
    {x c1 c2 c3 q s t : α}
    {first : D4LeftFirstReturn x c1 c2 c3 t 0}
    (input : D4SSwapCycleRenewalPacket x c1 c2 c3 q s t first)
    (newCycle : D4SSwapNewCycle x c1 c2 c3 q s t first) :
    Disjoint (d4SSwapSixFinset x c1 c2 c3 q s)
        (lxCycleFinset x t first.period) ∧
      Disjoint (d4SSwapSixFinset x c1 c2 c3 q s)
        (lxCycleFinset x newCycle.u newCycle.firstReturn.period) ∧
      Disjoint (lxCycleFinset x t first.period)
        (lxCycleFinset x newCycle.u newCycle.firstReturn.period) := by
  classical
  exact ⟨d4SSwapSixFinset_disjoint_lxCycleFinset input input.t_fresh first,
    d4SSwapSixFinset_disjoint_lxCycleFinset input newCycle.fresh
      newCycle.firstReturn,
    lxCycleFinset_disjoint_of_off_cycle first newCycle.firstReturn
      newCycle.off_t_cycle⟩

/-- Exact finite accounting in the fresh-cycle leaf, without assuming that the
generic parameters `q` and `s` are distinct. -/
theorem d4SSwapNewCycle_union_card_eq_named_add_periods
    {x c1 c2 c3 q s t : α}
    {first : D4LeftFirstReturn x c1 c2 c3 t 0}
    (input : D4SSwapCycleRenewalPacket x c1 c2 c3 q s t first)
    (newCycle : D4SSwapNewCycle x c1 c2 c3 q s t first) :
    ((d4SSwapSixFinset x c1 c2 c3 q s ∪
        lxCycleFinset x t first.period) ∪
      lxCycleFinset x newCycle.u newCycle.firstReturn.period).card =
      (d4SSwapSixFinset x c1 c2 c3 q s).card + first.period +
        newCycle.firstReturn.period := by
  classical
  rcases d4SSwapNewCycle_pairwiseDisjoint input newCycle with
    ⟨hnamed_t, hnamed_u, ht_u⟩
  rw [Finset.card_union_of_disjoint
      (Finset.disjoint_union_left.mpr ⟨hnamed_u, ht_u⟩),
    Finset.card_union_of_disjoint hnamed_t,
    card_lxCycleFinset_of_firstReturn first,
    card_lxCycleFinset_of_firstReturn newCycle.firstReturn]

/-- The strongest unconditional numerical bound supplied by the generic
renewal packet.  The D4 base and `q` give five distinct named points; `q ≠ s`
is not retained by this API. -/
theorem d4SSwapNewCycle_union_card_lower_bound
    {x c1 c2 c3 q s t : α}
    {first : D4LeftFirstReturn x c1 c2 c3 t 0}
    (input : D4SSwapCycleRenewalPacket x c1 c2 c3 q s t first)
    (newCycle : D4SSwapNewCycle x c1 c2 c3 q s t first) :
    5 + first.period + newCycle.firstReturn.period ≤
      ((d4SSwapSixFinset x c1 c2 c3 q s ∪
          lxCycleFinset x t first.period) ∪
        lxCycleFinset x newCycle.u newCycle.firstReturn.period).card := by
  rw [d4SSwapNewCycle_union_card_eq_named_add_periods input newCycle]
  have := d4SSwapSixFinset_card_lower_bound input
  omega

/-- If the missing named-point distinction is supplied explicitly, the fresh
cycle leaf has the expected exact size `6 + d_t + d_u`. -/
theorem d4SSwapNewCycle_union_card_of_q_ne_s
    {x c1 c2 c3 q s t : α}
    {first : D4LeftFirstReturn x c1 c2 c3 t 0}
    (input : D4SSwapCycleRenewalPacket x c1 c2 c3 q s t first)
    (newCycle : D4SSwapNewCycle x c1 c2 c3 q s t first)
    (q_ne_s : q ≠ s) :
    ((d4SSwapSixFinset x c1 c2 c3 q s ∪
        lxCycleFinset x t first.period) ∪
      lxCycleFinset x newCycle.u newCycle.firstReturn.period).card =
      6 + first.period + newCycle.firstReturn.period := by
  rw [d4SSwapNewCycle_union_card_eq_named_add_periods input newCycle,
    d4SSwapSixFinset_card_of_q_ne_s input q_ne_s]

/-- For the canonical S-swap terms, the tagged trace supplies the missing
named-point distinction, so the fresh-cycle leaf has exact size
`6 + d_t + d_u`. -/
theorem d4SSwapNewCycle_union_card_of_canonical
    {x c1 c2 c3 t : α}
    {first : D4LeftFirstReturn x c1 c2 c3 t 0}
    (input : D4SSwapCycleRenewalPacket x c1 c2 c3
      (c2 ◇ x) (c3 ◇ (c2 ◇ x)) t first)
    (newCycle : D4SSwapNewCycle x c1 c2 c3
      (c2 ◇ x) (c3 ◇ (c2 ◇ x)) t first) :
    ((d4SSwapSixFinset x c1 c2 c3 (c2 ◇ x) (c3 ◇ (c2 ◇ x)) ∪
        lxCycleFinset x t first.period) ∪
      lxCycleFinset x newCycle.u newCycle.firstReturn.period).card =
      6 + first.period + newCycle.firstReturn.period := by
  exact d4SSwapNewCycle_union_card_of_q_ne_s input newCycle
    input.traceStart.s_ne_q.symm

/-- Exact named-finset-plus-period accounting for the strict-growth constructor
of the explicit `q`-fixer transition.  The final hypothesis is the fixer's
equation retained by that constructor. -/
theorem d4SSwapQFixerStrictGrowth_union_card_eq_named_add_periods
    {x c1 c2 c3 q s t : α}
    {first : D4LeftFirstReturn x c1 c2 c3 t 0}
    (input : D4SSwapCycleRenewalPacket x c1 c2 c3 q s t first)
    (off_t_cycle : ∀ k, k < first.period →
      q ◇ (q ◇ x) ≠ LxPhase x t k)
    (pFirst : D4LeftFirstReturn x c1 c2 c3 (q ◇ (q ◇ x)) 0)
    (_p_fixes_q : (q ◇ (q ◇ x)) ◇ q = q) :
    ((d4SSwapSixFinset x c1 c2 c3 q s ∪
        lxCycleFinset x t first.period) ∪
      lxCycleFinset x (q ◇ (q ◇ x)) pFirst.period).card =
      (d4SSwapSixFinset x c1 c2 c3 q s).card + first.period +
        pFirst.period := by
  classical
  have hnamed_t :=
    d4SSwapSixFinset_disjoint_lxCycleFinset input input.t_fresh first
  have hnamed_p :=
    d4SSwapSixFinset_disjoint_lxCycleFinset input input.common.qFixer_fresh pFirst
  have ht_p := lxCycleFinset_disjoint_of_off_cycle first pFirst off_t_cycle
  rw [Finset.card_union_of_disjoint
      (Finset.disjoint_union_left.mpr ⟨hnamed_p, ht_p⟩),
    Finset.card_union_of_disjoint hnamed_t,
    card_lxCycleFinset_of_firstReturn first,
    card_lxCycleFinset_of_firstReturn pFirst]

/-- Unconditional numerical accounting for the strict-growth `q`-fixer leaf. -/
theorem d4SSwapQFixerStrictGrowth_union_card_lower_bound
    {x c1 c2 c3 q s t : α}
    {first : D4LeftFirstReturn x c1 c2 c3 t 0}
    (input : D4SSwapCycleRenewalPacket x c1 c2 c3 q s t first)
    (off_t_cycle : ∀ k, k < first.period →
      q ◇ (q ◇ x) ≠ LxPhase x t k)
    (pFirst : D4LeftFirstReturn x c1 c2 c3 (q ◇ (q ◇ x)) 0)
    (p_fixes_q : (q ◇ (q ◇ x)) ◇ q = q) :
    5 + first.period + pFirst.period ≤
      ((d4SSwapSixFinset x c1 c2 c3 q s ∪
          lxCycleFinset x t first.period) ∪
        lxCycleFinset x (q ◇ (q ◇ x)) pFirst.period).card := by
  rw [d4SSwapQFixerStrictGrowth_union_card_eq_named_add_periods input
    off_t_cycle pFirst p_fixes_q]
  have := d4SSwapSixFinset_card_lower_bound input
  omega

/-- With `q ≠ s` explicit, strict growth gives exactly `6 + d_t + d_p`
elements in the canonical disjoint union. -/
theorem d4SSwapQFixerStrictGrowth_union_card_of_q_ne_s
    {x c1 c2 c3 q s t : α}
    {first : D4LeftFirstReturn x c1 c2 c3 t 0}
    (input : D4SSwapCycleRenewalPacket x c1 c2 c3 q s t first)
    (off_t_cycle : ∀ k, k < first.period →
      q ◇ (q ◇ x) ≠ LxPhase x t k)
    (pFirst : D4LeftFirstReturn x c1 c2 c3 (q ◇ (q ◇ x)) 0)
    (p_fixes_q : (q ◇ (q ◇ x)) ◇ q = q)
    (q_ne_s : q ≠ s) :
    ((d4SSwapSixFinset x c1 c2 c3 q s ∪
        lxCycleFinset x t first.period) ∪
      lxCycleFinset x (q ◇ (q ◇ x)) pFirst.period).card =
      6 + first.period + pFirst.period := by
  rw [d4SSwapQFixerStrictGrowth_union_card_eq_named_add_periods input
      off_t_cycle pFirst p_fixes_q,
    d4SSwapSixFinset_card_of_q_ne_s input q_ne_s]

/-- For the canonical S-swap terms, strict `q`-fixer growth has exact size
`6 + d_t + d_p` without an additional named-point hypothesis. -/
theorem d4SSwapQFixerStrictGrowth_union_card_of_canonical
    {x c1 c2 c3 t : α}
    {first : D4LeftFirstReturn x c1 c2 c3 t 0}
    (input : D4SSwapCycleRenewalPacket x c1 c2 c3
      (c2 ◇ x) (c3 ◇ (c2 ◇ x)) t first)
    (off_t_cycle : ∀ k, k < first.period →
      (c2 ◇ x) ◇ ((c2 ◇ x) ◇ x) ≠ LxPhase x t k)
    (pFirst : D4LeftFirstReturn x c1 c2 c3
      ((c2 ◇ x) ◇ ((c2 ◇ x) ◇ x)) 0)
    (p_fixes_q : ((c2 ◇ x) ◇ ((c2 ◇ x) ◇ x)) ◇ (c2 ◇ x) = c2 ◇ x) :
    ((d4SSwapSixFinset x c1 c2 c3 (c2 ◇ x) (c3 ◇ (c2 ◇ x)) ∪
        lxCycleFinset x t first.period) ∪
      lxCycleFinset x ((c2 ◇ x) ◇ ((c2 ◇ x) ◇ x)) pFirst.period).card =
      6 + first.period + pFirst.period := by
  exact d4SSwapQFixerStrictGrowth_union_card_of_q_ne_s input off_t_cycle
    pFirst p_fixes_q input.traceStart.s_ne_q.symm

end

section
universe u
variable {alpha : Type u} [Magma' alpha]
set_option linter.unusedFintypeInType false in
/-- Produce the canonical one-step q-fixer seed and its exhaustive cycle
classification. -/
theorem e677_d4_s_swap_qFixerPumpOneStep [Fintype alpha]
    (h : E677 alpha)
    {x c1 c2 c3 q s t : alpha}
    {first : D4LeftFirstReturn x c1 c2 c3 t 0}
    (input : D4SSwapCycleRenewalPacket x c1 c2 c3 q s t first)
    (q_eq : q = c2 ◇ x)
    (s_eq : s = c3 ◇ q) :
    D4SSwapQFixerPumpPacket x c1 c2 c3 q s t
      (q ◇ (q ◇ x)) (q ◇ (q ◇ (q ◇ x))) first := by
  classical
  let p := q ◇ (q ◇ x)
  let u := q ◇ p
  change D4SSwapQFixerPumpPacket x c1 c2 c3 q s t p u first
  have hp_q : p ◇ q = q := input.common.qFixer_fixes_q
  have hp_fresh : E677FreshOutsideSix x c1 c2 c3 q s p :=
    input.common.qFixer_fresh
  have hq_return : c2 ◇ q = c1 := by
    rw [q_eq]
    exact input.basePacket.q_packet_return
  have hq_c1 : q ◇ c1 = x := by
    apply e677_left_cancel h c2
    have hsource := (h q c2).symm
    rw [hq_return, input.traceStart.r_eq_c1] at hsource
    exact hsource.trans q_eq
  have hc1_q : c1 ◇ q = x := by
    rw [q_eq]
    exact input.basePacket.q_packet_preimage
  have hq_ne_x : q ≠ x := by
    rw [q_eq]
    exact input.basePacket.q_ne_x
  have hq_ne_c1 : q ≠ c1 := by
    rw [q_eq]
    exact input.basePacket.q_ne_c1
  have hq_u : q ◇ u = q := by
    have hsource := (h q p).symm
    rw [hp_q] at hsource
    change p ◇ (q ◇ u) = q at hsource
    exact e677_left_cancel h p (hsource.trans hp_q.symm)
  have hu_x : u ≠ x := by
    intro hu
    apply hp_fresh.2.1
    apply e677_left_cancel h q
    calc
      q ◇ p = u := rfl
      _ = x := hu
      _ = q ◇ c1 := hq_c1.symm
  have hu_c1 : u ≠ c1 := by
    intro hu
    apply hq_ne_x
    have hq_c1_eq_q : q ◇ c1 = q := by simpa only [← hu] using hq_u
    exact hq_c1_eq_q.symm.trans hq_c1
  have hu_c2 : u ≠ c2 := by
    intro hu
    apply hq_ne_x
    have hc1q_q : c1 ◇ q = q := by
      have hsource := (h q c1).symm
      simpa only [hc1_q, input.basePacket.orbit_c2, ← hu, hq_u]
        using hsource
    exact hc1q_q.symm.trans hc1_q
  have hu_c3 : u ≠ c3 := by
    intro hu
    have hu_x_eq_q : u ◇ x = q := by
      rw [hu]
      exact input.basePacket.q_collision.symm.trans q_eq.symm
    have hu_q_eq_s : u ◇ q = s := by
      rw [hu]
      exact s_eq.symm
    have hx_u_eq_x : x ◇ u = x := by
      rw [hu]
      exact input.basePacket.orbit_closes
    have hu_s_eq_x : u ◇ s = x := by
      simpa only [hu_x_eq_q, hq_u, input.q_to_s] using (h x u).symm
    have hs_x_eq_q : s ◇ x = q := by
      apply e677_left_cancel h u
      have hsource : u ◇ (s ◇ x) = s := by
        simpa only [hu_s_eq_x, hx_u_eq_x]
          using (h s u).symm
      exact hsource.trans hu_q_eq_s.symm
    have hq_q_eq_s : q ◇ q = s := by
      apply e677_left_cancel h x
      calc
        x ◇ (q ◇ q) = q := by
          simpa only [input.q_to_s, hs_x_eq_q] using (h q x).symm
        _ = x ◇ s := input.s_to_q.symm
    let z := u ◇ ((q ◇ u) ◇ q)
    have hq_z_eq_u : q ◇ z = u := by
      simpa only [z] using (h u q).symm
    have hz_eq_x : z = x := by
      simp only [z, hq_u, hq_q_eq_s, hu_s_eq_x]
    have hs_eq_x : s = x := by
      have hsource := (h z q).symm
      rw [hq_z_eq_u, hu_q_eq_s, hz_eq_x, input.s_to_q, hq_q_eq_s] at hsource
      exact hsource
    apply input.traceStart.s_ne_x
    calc
      c3 ◇ (c2 ◇ x) = c3 ◇ q := by rw [q_eq]
      _ = s := s_eq.symm
      _ = x := hs_eq_x
  have hu_q : u ≠ q := by
    intro hu
    apply hp_fresh.2.2.2.2.1
    have hq_q : q ◇ q = q := by simpa only [hu] using hq_u
    exact (e677_fixer_unique h hp_q).trans (e677_fixer_unique h hq_q).symm
  have hu_s : u ≠ s := by
    intro hu
    have hx_u_eq_q : x ◇ u = q := by
      rw [hu]
      exact input.s_to_q
    have hq_ux_eq_u : q ◇ (u ◇ x) = u := by
      apply e677_left_cancel h x
      have hsource := (h q x).symm
      simpa only [input.q_to_s, ← hu] using hsource.trans hx_u_eq_q.symm
    have hp_eq_ux : p = u ◇ x := by
      apply e677_left_cancel h q
      exact (show q ◇ p = u from rfl).trans hq_ux_eq_u.symm
    have hp_eq_uqq : p = u ◇ (q ◇ q) := by
      apply e677_left_cancel h q
      have hsource := (h u q).symm
      simpa only [hq_u] using (show q ◇ p = u from rfl).trans hsource.symm
    have hx_eq_qq : x = q ◇ q := by
      apply e677_left_cancel h u
      exact hp_eq_ux.symm.trans hp_eq_uqq
    apply hq_ne_c1
    symm
    apply e677_left_cancel h q
    exact hq_c1.trans hx_eq_qq
  have hu_p : u ≠ p := by
    intro hu
    apply hp_fresh.2.2.2.2.1
    have hqp_q : q ◇ p = q := by rw [← hu]; exact hq_u
    calc
      p = u := hu.symm
      _ = q ◇ p := rfl
      _ = q := hqp_q
  have hu_not_fixes_q : u ◇ q ≠ q := by
    intro hu_fix
    apply hu_p
    exact (e677_fixer_unique h hu_fix).trans (e677_fixer_unique h hp_q).symm
  have hu_fresh : E677FreshOutsideSix x c1 c2 c3 q s u :=
    ⟨hu_x, hu_c1, hu_c2, hu_c3, hu_q, hu_s⟩
  have seed : D4SSwapQFixerPumpSeed x c1 c2 c3 q s p u :=
    ⟨hp_q, hp_fresh, hq_u, hu_fresh, hu_p, hu_not_fixes_q⟩
  have uFirst : D4LeftFirstReturn x c1 c2 c3 u 0 := by
    apply d4LeftFirstReturn_of_finite_leftInjective
      (e677_leftMul_inj h x)
      input.basePacket.orbit_c1 input.basePacket.orbit_c2
      input.basePacket.orbit_c3 input.basePacket.orbit_closes
    refine ⟨?_, ?_⟩
    · intro i hi
      have hi_zero : i = 0 := by omega
      subst i
      simpa only [Function.iterate_zero_apply] using
        ⟨hu_x, hu_c1, hu_c2, hu_c3⟩
    · intro i hi j hj _
      omega
  have transition : D4SSwapQFixerPumpTransition x c1 c2 c3 q t p u first := by
    rcases e677_d4_s_swap_qFixerCycleTransition h input with
      ⟨pPhase, pPhase_lt, p_eq, pPhase_fixes_q⟩ |
      ⟨p_off_t, pFirst, _p_fixes_q⟩
    · by_cases u_on_t : ∃ k, k < first.period ∧ u = LxPhase x t k
      · rcases u_on_t with ⟨uPhase, uPhase_lt, u_eq⟩
        exact .bothOnT pPhase uPhase pPhase_lt uPhase_lt p_eq u_eq
          pPhase_fixes_q (by
            intro phases_eq
            apply hu_p
            exact u_eq.trans (phases_eq ▸ p_eq.symm))
      · exact .pOnT_uEscape pPhase pPhase_lt p_eq pPhase_fixes_q
          (by intro k hk hu_eq; exact u_on_t ⟨k, hk, hu_eq⟩) uFirst
    · by_cases u_on_t : ∃ k, k < first.period ∧ u = LxPhase x t k
      · rcases u_on_t with ⟨uPhase, uPhase_lt, u_eq⟩
        exact .pNew_uOnT p_off_t pFirst uPhase uPhase_lt u_eq
      · by_cases u_on_p : ∃ k, k < pFirst.period ∧ u = LxPhase x p k
        · rcases u_on_p with ⟨uPhase, uPhase_lt, u_eq⟩
          have uPhase_pos : 0 < uPhase := by
            have uPhase_ne : uPhase ≠ 0 := by
              intro phase_zero
              subst uPhase
              apply hu_p
              simpa only [LxPhase, Function.iterate_zero_apply] using u_eq
            omega
          exact .pNew_uOnP p_off_t pFirst
            (by intro k hk hu_eq; exact u_on_t ⟨k, hk, hu_eq⟩)
            uPhase uPhase_pos uPhase_lt u_eq
        · exact .pNew_uEscape p_off_t pFirst
            (by intro k hk hu_eq; exact u_on_t ⟨k, hk, hu_eq⟩)
            (by intro k hk hu_eq; exact u_on_p ⟨k, hk, hu_eq⟩) uFirst
  exact ⟨input, q_eq, s_eq, seed, transition⟩

/-- In the `pOnT_uEscape` leaf, the named points, old `t`-cycle, and escaping
`u`-cycle are pairwise disjoint. -/
theorem d4SSwapQFixerPump_pOnT_uEscape_pairwiseDisjoint
    [DecidableEq alpha]
    {x c1 c2 c3 q s t p u : alpha}
    {first : D4LeftFirstReturn x c1 c2 c3 t 0}
    (packet : D4SSwapQFixerPumpPacket x c1 c2 c3 q s t p u first)
    (u_off_t : ∀ k, k < first.period → u ≠ LxPhase x t k)
    (uFirst : D4LeftFirstReturn x c1 c2 c3 u 0) :
    Disjoint (d4SSwapSixFinset x c1 c2 c3 q s)
        (lxCycleFinset x t first.period) ∧
      Disjoint (d4SSwapSixFinset x c1 c2 c3 q s)
        (lxCycleFinset x u uFirst.period) ∧
      Disjoint (lxCycleFinset x t first.period)
        (lxCycleFinset x u uFirst.period) := by
  exact ⟨d4SSwapSixFinset_disjoint_lxCycleFinset
      packet.input packet.input.t_fresh first,
    d4SSwapSixFinset_disjoint_lxCycleFinset
      packet.input packet.seed.u_fresh uFirst,
    lxCycleFinset_disjoint_of_off_cycle first uFirst u_off_t⟩

/-- Exact whole-union accounting in the `pOnT_uEscape` leaf. -/
theorem d4SSwapQFixerPump_pOnT_uEscape_union_card
    [DecidableEq alpha]
    {x c1 c2 c3 q s t p u : alpha}
    {first : D4LeftFirstReturn x c1 c2 c3 t 0}
    (packet : D4SSwapQFixerPumpPacket x c1 c2 c3 q s t p u first)
    (u_off_t : ∀ k, k < first.period → u ≠ LxPhase x t k)
    (uFirst : D4LeftFirstReturn x c1 c2 c3 u 0) :
    ((d4SSwapSixFinset x c1 c2 c3 q s ∪
        lxCycleFinset x t first.period) ∪
      lxCycleFinset x u uFirst.period).card =
      6 + first.period + uFirst.period := by
  have q_ne_s : q ≠ s := by
    intro q_eq_s
    apply packet.input.traceStart.s_ne_q
    calc
      c3 ◇ (c2 ◇ x) = c3 ◇ q := by rw [packet.q_eq]
      _ = s := packet.s_eq.symm
      _ = q := q_eq_s.symm
      _ = c2 ◇ x := packet.q_eq
  rcases d4SSwapQFixerPump_pOnT_uEscape_pairwiseDisjoint
      packet u_off_t uFirst with ⟨hnamed_t, hnamed_u, ht_u⟩
  rw [Finset.card_union_of_disjoint
      (Finset.disjoint_union_left.mpr ⟨hnamed_u, ht_u⟩),
    Finset.card_union_of_disjoint hnamed_t,
    card_lxCycleFinset_of_firstReturn first,
    card_lxCycleFinset_of_firstReturn uFirst,
    d4SSwapSixFinset_card_of_q_ne_s packet.input q_ne_s]

/-- In the `pNew_uEscape` leaf, the named points and the three retained finite
cycles are pairwise disjoint. -/
theorem d4SSwapQFixerPump_pNew_uEscape_pairwiseDisjoint
    [DecidableEq alpha]
    {x c1 c2 c3 q s t p u : alpha}
    {first : D4LeftFirstReturn x c1 c2 c3 t 0}
    (packet : D4SSwapQFixerPumpPacket x c1 c2 c3 q s t p u first)
    (p_off_t : ∀ k, k < first.period → p ≠ LxPhase x t k)
    (pFirst : D4LeftFirstReturn x c1 c2 c3 p 0)
    (u_off_t : ∀ k, k < first.period → u ≠ LxPhase x t k)
    (u_off_p : ∀ k, k < pFirst.period → u ≠ LxPhase x p k)
    (uFirst : D4LeftFirstReturn x c1 c2 c3 u 0) :
    Disjoint (d4SSwapSixFinset x c1 c2 c3 q s)
        (lxCycleFinset x t first.period) ∧
      Disjoint (d4SSwapSixFinset x c1 c2 c3 q s)
        (lxCycleFinset x p pFirst.period) ∧
      Disjoint (d4SSwapSixFinset x c1 c2 c3 q s)
        (lxCycleFinset x u uFirst.period) ∧
      Disjoint (lxCycleFinset x t first.period)
        (lxCycleFinset x p pFirst.period) ∧
      Disjoint (lxCycleFinset x t first.period)
        (lxCycleFinset x u uFirst.period) ∧
      Disjoint (lxCycleFinset x p pFirst.period)
        (lxCycleFinset x u uFirst.period) := by
  exact ⟨d4SSwapSixFinset_disjoint_lxCycleFinset
      packet.input packet.input.t_fresh first,
    d4SSwapSixFinset_disjoint_lxCycleFinset
      packet.input packet.seed.p_fresh pFirst,
    d4SSwapSixFinset_disjoint_lxCycleFinset
      packet.input packet.seed.u_fresh uFirst,
    lxCycleFinset_disjoint_of_off_cycle first pFirst p_off_t,
    lxCycleFinset_disjoint_of_off_cycle first uFirst u_off_t,
    lxCycleFinset_disjoint_of_off_cycle pFirst uFirst u_off_p⟩

/-- Exact whole-union accounting in the `pNew_uEscape` leaf. -/
theorem d4SSwapQFixerPump_pNew_uEscape_union_card
    [DecidableEq alpha]
    {x c1 c2 c3 q s t p u : alpha}
    {first : D4LeftFirstReturn x c1 c2 c3 t 0}
    (packet : D4SSwapQFixerPumpPacket x c1 c2 c3 q s t p u first)
    (p_off_t : ∀ k, k < first.period → p ≠ LxPhase x t k)
    (pFirst : D4LeftFirstReturn x c1 c2 c3 p 0)
    (u_off_t : ∀ k, k < first.period → u ≠ LxPhase x t k)
    (u_off_p : ∀ k, k < pFirst.period → u ≠ LxPhase x p k)
    (uFirst : D4LeftFirstReturn x c1 c2 c3 u 0) :
    (((d4SSwapSixFinset x c1 c2 c3 q s ∪
          lxCycleFinset x t first.period) ∪
        lxCycleFinset x p pFirst.period) ∪
      lxCycleFinset x u uFirst.period).card =
      6 + first.period + pFirst.period + uFirst.period := by
  have q_ne_s : q ≠ s := by
    intro q_eq_s
    apply packet.input.traceStart.s_ne_q
    calc
      c3 ◇ (c2 ◇ x) = c3 ◇ q := by rw [packet.q_eq]
      _ = s := packet.s_eq.symm
      _ = q := q_eq_s.symm
      _ = c2 ◇ x := packet.q_eq
  rcases d4SSwapQFixerPump_pNew_uEscape_pairwiseDisjoint
      packet p_off_t pFirst u_off_t u_off_p uFirst with
    ⟨hnamed_t, hnamed_p, hnamed_u, ht_p, ht_u, hp_u⟩
  rw [Finset.card_union_of_disjoint
      (Finset.disjoint_union_left.mpr
        ⟨Finset.disjoint_union_left.mpr ⟨hnamed_u, ht_u⟩, hp_u⟩),
    Finset.card_union_of_disjoint
      (Finset.disjoint_union_left.mpr ⟨hnamed_p, ht_p⟩),
    Finset.card_union_of_disjoint hnamed_t,
    card_lxCycleFinset_of_firstReturn first,
    card_lxCycleFinset_of_firstReturn pFirst,
    card_lxCycleFinset_of_firstReturn uFirst,
    d4SSwapSixFinset_card_of_q_ne_s packet.input q_ne_s]

end

end FiniteMagmaE677.SSwap

section
/- Standalone source export: q-square refinement in the D4 S-swap branch.
   This fragment intentionally has no imports; prepend the shared SSwap core. -/

section
universe u

namespace FiniteMagmaE677.SSwap
local infixl:65 " ◇ " => Magma'.op

variable {alpha : Type u} [Magma' alpha]

theorem e677_d4_s_swap_qSquareSeed [Fintype alpha]
    (h : E677 alpha)
    {x c1 c2 c3 q s t : alpha}
    {first : D4LeftFirstReturn x c1 c2 c3 t 0}
    (input : D4SSwapCycleRenewalPacket x c1 c2 c3 q s t first)
    (q_eq : q = c2 ◇ x)
    (s_eq : s = c3 ◇ q) :
    D4SSwapQSquareSeed x c1 c2 c3 q s
      (q ◇ (q ◇ x)) (q ◇ (q ◇ (q ◇ x))) := by
  let p := q ◇ (q ◇ x)
  let u := q ◇ p
  change D4SSwapQSquareSeed x c1 c2 c3 q s p u
  have pump : D4SSwapQFixerPumpPacket x c1 c2 c3 q s t p u first :=
    e677_d4_s_swap_qFixerPumpOneStep h input q_eq s_eq
  have hq_return : c2 ◇ q = c1 := by
    rw [q_eq]
    exact input.basePacket.q_packet_return
  have hq_c1 : q ◇ c1 = x := by
    apply e677_left_cancel h c2
    have hsource := (h q c2).symm
    rw [hq_return, input.traceStart.r_eq_c1] at hsource
    exact hsource.trans q_eq
  have hc1_q : c1 ◇ q = x := by
    rw [q_eq]
    exact input.basePacket.q_packet_preimage
  have hp_factor : p = u ◇ (q ◇ q) := by
    apply e677_left_cancel h q
    have hsource := (h u q).symm
    simpa only [pump.seed.q_mul_u_eq_q] using
      (show q ◇ p = u from rfl).trans hsource.symm
  have hv_x : q ◇ q ≠ x := by
    intro hv
    apply input.basePacket.q_ne_c1
    rw [← q_eq]
    exact e677_left_cancel h q (hv.trans hq_c1.symm)
  have hv_c1 : q ◇ q ≠ c1 := by
    intro hv
    apply pump.seed.p_fresh.2.2.2.2.1
    calc
      p = q ◇ (q ◇ x) := rfl
      _ = q ◇ (q ◇ (c1 ◇ q)) := by rw [hc1_q]
      _ = q ◇ (q ◇ ((q ◇ q) ◇ q)) := by rw [hv]
      _ = q := (h q q).symm
  have hv_c2 : q ◇ q ≠ c2 := by
    intro hv
    have hu_expand : u = q ◇ (u ◇ c2) := by
      simpa only [pump.seed.q_mul_u_eq_q, hv] using h u q
    have hq_expand : q = q ◇ (q ◇ c1) := by
      simpa only [hv, hq_return] using h q q
    have hu_eq_qc1 : u = q ◇ c1 := by
      apply e677_left_cancel h q
      exact pump.seed.q_mul_u_eq_q.trans hq_expand
    have hu_c2 : u ◇ c2 = c1 := by
      apply e677_left_cancel h q
      exact hu_expand.symm.trans hu_eq_qc1
    apply pump.seed.p_fresh.2.1
    calc
      p = u ◇ (q ◇ q) := hp_factor
      _ = u ◇ c2 := by rw [hv]
      _ = c1 := hu_c2
  have hv_c3 : q ◇ q ≠ c3 := by
    intro hv
    have hu_expand : u = q ◇ (u ◇ c3) := by
      simpa only [pump.seed.q_mul_u_eq_q, hv] using h u q
    have hq_expand : q = q ◇ (q ◇ s) := by
      simpa only [hv, s_eq] using h q q
    have hu_eq_qs : u = q ◇ s := by
      apply e677_left_cancel h q
      exact pump.seed.q_mul_u_eq_q.trans hq_expand
    have hu_c3 : u ◇ c3 = s := by
      apply e677_left_cancel h q
      exact hu_expand.symm.trans hu_eq_qs
    apply pump.seed.p_fresh.2.2.2.2.2
    calc
      p = u ◇ (q ◇ q) := hp_factor
      _ = u ◇ c3 := by rw [hv]
      _ = s := hu_c3
  have hv_q : q ◇ q ≠ q := by
    intro hv
    apply pump.seed.u_fresh.2.2.2.2.1
    exact e677_left_cancel h q
      (pump.seed.q_mul_u_eq_q.trans hv.symm)
  have hv_s : q ◇ q ≠ s := by
    intro hv
    have hs_qx : s ◇ (q ◇ x) = q := by
      apply e677_left_cancel h x
      simpa only [input.s_to_q] using
        (h s x).symm.trans input.q_to_s.symm
    have hs_qc1_ne_q : s ◇ (q ◇ c1) ≠ q := by
      intro heq
      apply input.basePacket.x_ne_c1
      exact (e677_left_cancel h q
        (e677_left_cancel h s (heq.trans hs_qx.symm))).symm
    have hq_sqc1_ne_s : q ◇ (s ◇ (q ◇ c1)) ≠ s := by
      intro heq
      apply hs_qc1_ne_q
      exact e677_left_cancel h q (heq.trans hv.symm)
    have hx_qsqc1_ne_q : x ◇ (q ◇ (s ◇ (q ◇ c1))) ≠ q := by
      intro heq
      apply hq_sqc1_ne_s
      exact e677_left_cancel h x (heq.trans input.s_to_q.symm)
    apply hx_qsqc1_ne_q
    simpa only [input.q_to_s, hq_c1] using (h q x).symm
  have hv_p : q ◇ q ≠ p := by
    intro hv
    have hq_qx : q = q ◇ x := by
      apply e677_left_cancel h q
      exact hv
    apply pump.seed.u_fresh.1
    apply e677_left_cancel h q
    exact pump.seed.q_mul_u_eq_q.trans hq_qx
  have hv_u : q ◇ q ≠ u := by
    intro hv
    apply pump.seed.p_fresh.2.2.2.2.1
    apply e677_left_cancel h q
    exact (hv.trans (show u = q ◇ p from rfl)).symm
  exact ⟨hp_factor, ⟨hv_x, hv_c1, hv_c2, hv_c3, hv_q, hv_s⟩, hv_p, hv_u⟩


theorem e677_d4_s_swap_bothOnT_qSquareReduction [Fintype alpha]
    (h : E677 alpha)
    {x c1 c2 c3 q s t : alpha}
    {first : D4LeftFirstReturn x c1 c2 c3 t 0}
    (pump : D4SSwapQFixerPumpPacket x c1 c2 c3 q s t
      (q ◇ (q ◇ x)) (q ◇ (q ◇ (q ◇ x))) first)
    (j l : Nat)
    (j_lt : j < first.period)
    (l_lt : l < first.period)
    (p_eq : q ◇ (q ◇ x) = LxPhase x t j)
    (u_eq : q ◇ (q ◇ (q ◇ x)) = LxPhase x t l)
    (_j_fixes_q : LxPhase x t j ◇ q = q)
    (j_ne_l : j ≠ l) :
    D4SSwapBothOnTQSquareReduction x c1 c2 c3 q s t
      (q ◇ (q ◇ x)) (q ◇ (q ◇ (q ◇ x))) first := by
  have seed := e677_d4_s_swap_qSquareSeed h pump.input pump.q_eq pump.s_eq
  by_cases on_t : ∃ m, m < first.period ∧ q ◇ q = LxPhase x t m
  · rcases on_t with ⟨m, m_lt, v_eq⟩
    have j_ne_m : j ≠ m := by
      intro hjm
      apply seed.ne_p
      calc
        q ◇ q = LxPhase x t m := v_eq
        _ = LxPhase x t j := by rw [hjm]
        _ = q ◇ (q ◇ x) := p_eq.symm
    have l_ne_m : l ≠ m := by
      intro hlm
      apply seed.ne_u
      calc
        q ◇ q = LxPhase x t m := v_eq
        _ = LxPhase x t l := by rw [hlm]
        _ = q ◇ (q ◇ (q ◇ x)) := u_eq.symm
    exact .threePhase j l m j_lt l_lt m_lt p_eq u_eq v_eq
      ⟨j_ne_l, j_ne_m, l_ne_m⟩ (by
        calc
          LxPhase x t j = q ◇ (q ◇ x) := p_eq.symm
          _ = (q ◇ (q ◇ (q ◇ x))) ◇ (q ◇ q) := seed.factor
          _ = LxPhase x t l ◇ LxPhase x t m := by rw [u_eq, v_eq])
  · have off_t : ∀ m, m < first.period →
        q ◇ q ≠ LxPhase x t m := by
      intro m m_lt v_eq
      exact on_t ⟨m, m_lt, v_eq⟩
    have vFirst : D4LeftFirstReturn x c1 c2 c3 (q ◇ q) 0 := by
      apply d4LeftFirstReturn_of_finite_leftInjective
        (e677_leftMul_inj h x)
        pump.input.basePacket.orbit_c1 pump.input.basePacket.orbit_c2
        pump.input.basePacket.orbit_c3 pump.input.basePacket.orbit_closes
      refine ⟨?_, ?_⟩
      · intro i hi
        have hi_zero : i = 0 := by omega
        subst i
        simpa only [Function.iterate_zero_apply] using
          ⟨seed.fresh.1, seed.fresh.2.1, seed.fresh.2.2.1,
            seed.fresh.2.2.2.1⟩
      · intro i hi k hk _
        omega
    exact .strictGrowth seed.fresh off_t vFirst

theorem d4SSwapBothOnTQSquare_strictGrowth_union_card
    [DecidableEq alpha]
    {x c1 c2 c3 q s t : alpha}
    {first : D4LeftFirstReturn x c1 c2 c3 t 0}
    (pump : D4SSwapQFixerPumpPacket x c1 c2 c3 q s t
      (q ◇ (q ◇ x)) (q ◇ (q ◇ (q ◇ x))) first)
    (fresh : E677FreshOutsideSix x c1 c2 c3 q s (q ◇ q))
    (off_t_cycle : ∀ m, m < first.period →
      q ◇ q ≠ LxPhase x t m)
    (vFirst : D4LeftFirstReturn x c1 c2 c3 (q ◇ q) 0) :
    ((d4SSwapSixFinset x c1 c2 c3 q s ∪
        lxCycleFinset x t first.period) ∪
      lxCycleFinset x (q ◇ q) vFirst.period).card =
      6 + first.period + vFirst.period := by
  have q_ne_s : q ≠ s := by
    intro q_eq_s
    apply pump.input.traceStart.s_ne_q
    calc
      c3 ◇ (c2 ◇ x) = c3 ◇ q := by rw [pump.q_eq]
      _ = s := pump.s_eq.symm
      _ = q := q_eq_s.symm
      _ = c2 ◇ x := pump.q_eq
  have hnamed_t := d4SSwapSixFinset_disjoint_lxCycleFinset
    pump.input pump.input.t_fresh first
  have hnamed_v := d4SSwapSixFinset_disjoint_lxCycleFinset
    pump.input fresh vFirst
  have ht_v := lxCycleFinset_disjoint_of_off_cycle
    first vFirst off_t_cycle
  rw [Finset.card_union_of_disjoint
      (Finset.disjoint_union_left.mpr ⟨hnamed_v, ht_v⟩),
    Finset.card_union_of_disjoint hnamed_t,
    card_lxCycleFinset_of_firstReturn first,
    card_lxCycleFinset_of_firstReturn vFirst,
    d4SSwapSixFinset_card_of_q_ne_s pump.input q_ne_s]

theorem e677_d4_s_swap_qFixerPump_qSquareOutcome [Fintype alpha]
    (h : E677 alpha)
    {x c1 c2 c3 q s t : alpha}
    {first : D4LeftFirstReturn x c1 c2 c3 t 0}
    (pump : D4SSwapQFixerPumpPacket x c1 c2 c3 q s t
      (q ◇ (q ◇ x)) (q ◇ (q ◇ (q ◇ x))) first) :
    D4SSwapQFixerPumpQSquareOutcome x c1 c2 c3 q s t
      (q ◇ (q ◇ x)) (q ◇ (q ◇ (q ◇ x))) first := by
  rcases pump.transition with
    ⟨pPhase, uPhase, pPhase_lt, uPhase_lt, p_eq, u_eq,
      pPhase_fixes_q, pPhase_ne_uPhase⟩ |
    ⟨pPhase, pPhase_lt, p_eq, pPhase_fixes_q, u_off_t, uFirst⟩ |
    ⟨p_off_t, pFirst, uPhase, uPhase_lt, u_eq⟩ |
    ⟨p_off_t, pFirst, u_off_t, uPhase, uPhase_pos, uPhase_lt, u_eq⟩ |
    ⟨p_off_t, pFirst, u_off_t, u_off_p, uFirst⟩
  · exact .bothOnT pump pPhase uPhase pPhase_lt uPhase_lt p_eq u_eq
      pPhase_fixes_q pPhase_ne_uPhase
      (e677_d4_s_swap_bothOnT_qSquareReduction h pump
        pPhase uPhase pPhase_lt uPhase_lt p_eq u_eq
        pPhase_fixes_q pPhase_ne_uPhase)
  · exact .pOnT_uEscape pump pPhase pPhase_lt p_eq pPhase_fixes_q
      u_off_t uFirst
  · exact .pNew_uOnT pump p_off_t pFirst uPhase uPhase_lt u_eq
  · exact .pNew_uOnP pump p_off_t pFirst u_off_t uPhase uPhase_pos
      uPhase_lt u_eq
  · exact .pNew_uEscape pump p_off_t pFirst u_off_t u_off_p uFirst

private noncomputable def d4SSwapQSquare_firstReturn_of_seed [Fintype alpha]
    (h : E677 alpha)
    {x c1 c2 c3 q s t p u : alpha}
    {first : D4LeftFirstReturn x c1 c2 c3 t 0}
    (pump : D4SSwapQFixerPumpPacket x c1 c2 c3 q s t p u first)
    (seed : D4SSwapQSquareSeed x c1 c2 c3 q s p u) :
    D4LeftFirstReturn x c1 c2 c3 (q ◇ q) 0 := by
  apply d4LeftFirstReturn_of_finite_leftInjective
    (e677_leftMul_inj h x)
    pump.input.basePacket.orbit_c1 pump.input.basePacket.orbit_c2
    pump.input.basePacket.orbit_c3 pump.input.basePacket.orbit_closes
  refine ⟨?_, ?_⟩
  · intro i hi
    have hi_zero : i = 0 := by omega
    subst i
    simpa only [Function.iterate_zero_apply] using
      ⟨seed.fresh.1, seed.fresh.2.1, seed.fresh.2.2.1,
        seed.fresh.2.2.2.1⟩
  · intro i hi k hk _
    omega

set_option linter.unusedFintypeInType false in
/-- Classify `q ◇ q` against both retained cycles in `pNew_uOnT`, preserving
phase zero and the orientation `p = u ◇ (q ◇ q)`. -/
theorem e677_d4_s_swap_pNew_uOnT_qSquareReduction [Fintype alpha]
    (h : E677 alpha)
    {x c1 c2 c3 q s t : alpha}
    {first : D4LeftFirstReturn x c1 c2 c3 t 0}
    (pump : D4SSwapQFixerPumpPacket x c1 c2 c3 q s t
      (q ◇ (q ◇ x)) (q ◇ (q ◇ (q ◇ x))) first)
    (_p_off_t : ∀ k, k < first.period → q ◇ (q ◇ x) ≠ LxPhase x t k)
    (pFirst : D4LeftFirstReturn x c1 c2 c3 (q ◇ (q ◇ x)) 0)
    (l : Nat)
    (l_lt : l < first.period)
    (u_eq : q ◇ (q ◇ (q ◇ x)) = LxPhase x t l) :
    D4SSwapPNewUOnTQSquareReduction x c1 c2 c3 q s t
      (q ◇ (q ◇ x)) (q ◇ (q ◇ (q ◇ x))) first pFirst := by
  have seed := e677_d4_s_swap_qSquareSeed h pump.input pump.q_eq pump.s_eq
  by_cases on_t : ∃ m, m < first.period ∧ q ◇ q = LxPhase x t m
  · rcases on_t with ⟨m, m_lt, v_eq⟩
    have l_ne_m : l ≠ m := by
      intro hlm
      apply seed.ne_u
      calc
        q ◇ q = LxPhase x t m := v_eq
        _ = LxPhase x t l := by rw [hlm]
        _ = q ◇ (q ◇ (q ◇ x)) := u_eq.symm
    exact .vOnT l m l_lt m_lt u_eq v_eq l_ne_m (by
      calc
        q ◇ (q ◇ x) = (q ◇ (q ◇ (q ◇ x))) ◇ (q ◇ q) := seed.factor
        _ = LxPhase x t l ◇ LxPhase x t m := by rw [u_eq, v_eq])
  · have off_t : ∀ m, m < first.period → q ◇ q ≠ LxPhase x t m := by
      intro m m_lt v_eq
      exact on_t ⟨m, m_lt, v_eq⟩
    by_cases on_p : ∃ m, m < pFirst.period ∧
        q ◇ q = LxPhase x (q ◇ (q ◇ x)) m
    · rcases on_p with ⟨m, m_lt, v_eq⟩
      have m_pos : 0 < m := by
        have m_ne_zero : m ≠ 0 := by
          intro hm
          subst m
          apply seed.ne_p
          simpa only [LxPhase, Function.iterate_zero_apply] using v_eq
        omega
      exact .vOnP l m l_lt m_pos m_lt u_eq v_eq (by
        calc
          q ◇ (q ◇ x) = (q ◇ (q ◇ (q ◇ x))) ◇ (q ◇ q) := seed.factor
          _ = LxPhase x t l ◇ LxPhase x (q ◇ (q ◇ x)) m := by
            rw [u_eq, v_eq])
    · have off_p : ∀ m, m < pFirst.period →
          q ◇ q ≠ LxPhase x (q ◇ (q ◇ x)) m := by
        intro m m_lt v_eq
        exact on_p ⟨m, m_lt, v_eq⟩
      exact .strictGrowth seed.fresh off_t off_p
        (d4SSwapQSquare_firstReturn_of_seed h pump seed)

set_option linter.unusedFintypeInType false in
/-- Classify `q ◇ q` against both retained cycles in `pNew_uOnP`, preserving
the positive old `p`-phase and the orientation `p = u ◇ (q ◇ q)`. -/
theorem e677_d4_s_swap_pNew_uOnP_qSquareReduction [Fintype alpha]
    (h : E677 alpha)
    {x c1 c2 c3 q s t : alpha}
    {first : D4LeftFirstReturn x c1 c2 c3 t 0}
    (pump : D4SSwapQFixerPumpPacket x c1 c2 c3 q s t
      (q ◇ (q ◇ x)) (q ◇ (q ◇ (q ◇ x))) first)
    (_p_off_t : ∀ k, k < first.period → q ◇ (q ◇ x) ≠ LxPhase x t k)
    (pFirst : D4LeftFirstReturn x c1 c2 c3 (q ◇ (q ◇ x)) 0)
    (_u_off_t : ∀ k, k < first.period →
      q ◇ (q ◇ (q ◇ x)) ≠ LxPhase x t k)
    (l : Nat)
    (l_pos : 0 < l)
    (l_lt : l < pFirst.period)
    (u_eq : q ◇ (q ◇ (q ◇ x)) = LxPhase x (q ◇ (q ◇ x)) l) :
    D4SSwapPNewUOnPQSquareReduction x c1 c2 c3 q s t
      (q ◇ (q ◇ x)) (q ◇ (q ◇ (q ◇ x))) first pFirst := by
  have seed := e677_d4_s_swap_qSquareSeed h pump.input pump.q_eq pump.s_eq
  by_cases on_t : ∃ m, m < first.period ∧ q ◇ q = LxPhase x t m
  · rcases on_t with ⟨m, m_lt, v_eq⟩
    exact .vOnT l m l_pos l_lt m_lt u_eq v_eq (by
      calc
        q ◇ (q ◇ x) = (q ◇ (q ◇ (q ◇ x))) ◇ (q ◇ q) := seed.factor
        _ = LxPhase x (q ◇ (q ◇ x)) l ◇ LxPhase x t m := by
          rw [u_eq, v_eq])
  · have off_t : ∀ m, m < first.period → q ◇ q ≠ LxPhase x t m := by
      intro m m_lt v_eq
      exact on_t ⟨m, m_lt, v_eq⟩
    by_cases on_p : ∃ m, m < pFirst.period ∧
        q ◇ q = LxPhase x (q ◇ (q ◇ x)) m
    · rcases on_p with ⟨m, m_lt, v_eq⟩
      have m_pos : 0 < m := by
        have m_ne_zero : m ≠ 0 := by
          intro hm
          subst m
          apply seed.ne_p
          simpa only [LxPhase, Function.iterate_zero_apply] using v_eq
        omega
      have l_ne_m : l ≠ m := by
        intro hlm
        apply seed.ne_u
        calc
          q ◇ q = LxPhase x (q ◇ (q ◇ x)) m := v_eq
          _ = LxPhase x (q ◇ (q ◇ x)) l := by rw [hlm]
          _ = q ◇ (q ◇ (q ◇ x)) := u_eq.symm
      exact .vOnP l m l_pos l_lt m_pos m_lt u_eq v_eq l_ne_m (by
        calc
          q ◇ (q ◇ x) = (q ◇ (q ◇ (q ◇ x))) ◇ (q ◇ q) := seed.factor
          _ = LxPhase x (q ◇ (q ◇ x)) l ◇
              LxPhase x (q ◇ (q ◇ x)) m := by rw [u_eq, v_eq])
    · have off_p : ∀ m, m < pFirst.period →
          q ◇ q ≠ LxPhase x (q ◇ (q ◇ x)) m := by
        intro m m_lt v_eq
        exact on_p ⟨m, m_lt, v_eq⟩
      exact .strictGrowth seed.fresh off_t off_p
        (d4SSwapQSquare_firstReturn_of_seed h pump seed)


theorem d4SSwapPNew_qSquare_contact_slack_drop [DecidableEq alpha]
    {x c1 c2 c3 q s t p u : alpha}
    {first : D4LeftFirstReturn x c1 c2 c3 t 0}
    {pFirst : D4LeftFirstReturn x c1 c2 c3 p 0}
    (seed : D4SSwapQSquareSeed x c1 c2 c3 q s p u)
    (on_accounted : q ◇ q ∈
      lxCycleFinset x t first.period ∪ lxCycleFinset x p pFirst.period) :
    d4SSwapPNewMarkedPhaseSlack x t p first.period pFirst.period {p, u, q ◇ q} + 1 =
      d4SSwapPNewMarkedPhaseSlack x t p first.period pFirst.period {p, u} := by
  let cycles := lxCycleFinset x t first.period ∪ lxCycleFinset x p pFirst.period
  have hv_mem : q ◇ q ∈ cycles \ {p, u} := by
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨on_accounted, not_or_intro seed.ne_p seed.ne_u⟩
  have hdiff : cycles \ {p, u, q ◇ q} = (cycles \ {p, u}).erase (q ◇ q) := by
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_erase]
    aesop
  change (cycles \ {p, u, q ◇ q}).card + 1 = (cycles \ {p, u}).card
  rw [hdiff]
  exact Finset.card_erase_add_one hv_mem

/-- Pairwise disjointness of the named six and all three retained cycles in a
strict-growth leaf.  It is accounting only: no fixer, iteration, or closure. -/
theorem d4SSwapPNewQSquare_strictGrowth_pairwiseDisjoint
    [DecidableEq alpha]
    {x c1 c2 c3 q s t p u : alpha}
    {first : D4LeftFirstReturn x c1 c2 c3 t 0}
    (pump : D4SSwapQFixerPumpPacket x c1 c2 c3 q s t p u first)
    (p_off_t : ∀ k, k < first.period → p ≠ LxPhase x t k)
    (pFirst : D4LeftFirstReturn x c1 c2 c3 p 0)
    (fresh : E677FreshOutsideSix x c1 c2 c3 q s (q ◇ q))
    (v_off_t : ∀ k, k < first.period → q ◇ q ≠ LxPhase x t k)
    (v_off_p : ∀ k, k < pFirst.period → q ◇ q ≠ LxPhase x p k)
    (vFirst : D4LeftFirstReturn x c1 c2 c3 (q ◇ q) 0) :
    Disjoint (d4SSwapSixFinset x c1 c2 c3 q s)
        (lxCycleFinset x t first.period) ∧
      Disjoint (d4SSwapSixFinset x c1 c2 c3 q s)
        (lxCycleFinset x p pFirst.period) ∧
      Disjoint (d4SSwapSixFinset x c1 c2 c3 q s)
        (lxCycleFinset x (q ◇ q) vFirst.period) ∧
      Disjoint (lxCycleFinset x t first.period)
        (lxCycleFinset x p pFirst.period) ∧
      Disjoint (lxCycleFinset x t first.period)
        (lxCycleFinset x (q ◇ q) vFirst.period) ∧
      Disjoint (lxCycleFinset x p pFirst.period)
        (lxCycleFinset x (q ◇ q) vFirst.period) := by
  exact ⟨d4SSwapSixFinset_disjoint_lxCycleFinset
      pump.input pump.input.t_fresh first,
    d4SSwapSixFinset_disjoint_lxCycleFinset
      pump.input pump.seed.p_fresh pFirst,
    d4SSwapSixFinset_disjoint_lxCycleFinset pump.input fresh vFirst,
    lxCycleFinset_disjoint_of_off_cycle first pFirst p_off_t,
    lxCycleFinset_disjoint_of_off_cycle first vFirst v_off_t,
    lxCycleFinset_disjoint_of_off_cycle pFirst vFirst v_off_p⟩

/-- Exact cardinality of the named six together with the old `t`-cycle, the
`p`-cycle, and the strict-growth `q ◇ q`-cycle. -/
theorem d4SSwapPNewQSquare_strictGrowth_union_card
    [DecidableEq alpha]
    {x c1 c2 c3 q s t p u : alpha}
    {first : D4LeftFirstReturn x c1 c2 c3 t 0}
    (pump : D4SSwapQFixerPumpPacket x c1 c2 c3 q s t p u first)
    (p_off_t : ∀ k, k < first.period → p ≠ LxPhase x t k)
    (pFirst : D4LeftFirstReturn x c1 c2 c3 p 0)
    (fresh : E677FreshOutsideSix x c1 c2 c3 q s (q ◇ q))
    (v_off_t : ∀ k, k < first.period → q ◇ q ≠ LxPhase x t k)
    (v_off_p : ∀ k, k < pFirst.period → q ◇ q ≠ LxPhase x p k)
    (vFirst : D4LeftFirstReturn x c1 c2 c3 (q ◇ q) 0) :
    (((d4SSwapSixFinset x c1 c2 c3 q s ∪
          lxCycleFinset x t first.period) ∪
        lxCycleFinset x p pFirst.period) ∪
      lxCycleFinset x (q ◇ q) vFirst.period).card =
      6 + first.period + pFirst.period + vFirst.period := by
  have q_ne_s : q ≠ s := by
    intro q_eq_s
    apply pump.input.traceStart.s_ne_q
    calc
      c3 ◇ (c2 ◇ x) = c3 ◇ q := by rw [pump.q_eq]
      _ = s := pump.s_eq.symm
      _ = q := q_eq_s.symm
      _ = c2 ◇ x := pump.q_eq
  rcases d4SSwapPNewQSquare_strictGrowth_pairwiseDisjoint
      pump p_off_t pFirst fresh v_off_t v_off_p vFirst with
    ⟨hnamed_t, hnamed_p, hnamed_v, ht_p, ht_v, hp_v⟩
  rw [Finset.card_union_of_disjoint
      (Finset.disjoint_union_left.mpr
        ⟨Finset.disjoint_union_left.mpr ⟨hnamed_v, ht_v⟩, hp_v⟩),
    Finset.card_union_of_disjoint
      (Finset.disjoint_union_left.mpr ⟨hnamed_p, ht_p⟩),
    Finset.card_union_of_disjoint hnamed_t,
    card_lxCycleFinset_of_firstReturn first,
    card_lxCycleFinset_of_firstReturn pFirst,
    card_lxCycleFinset_of_firstReturn vFirst,
    d4SSwapSixFinset_card_of_q_ne_s pump.input q_ne_s]

theorem e677_d4_s_swap_qFixerPump_pNewQSquareOutcome [Fintype alpha]
    (h : E677 alpha)
    {x c1 c2 c3 q s t : alpha}
    {first : D4LeftFirstReturn x c1 c2 c3 t 0}
    (pump : D4SSwapQFixerPumpPacket x c1 c2 c3 q s t
      (q ◇ (q ◇ x)) (q ◇ (q ◇ (q ◇ x))) first) :
    D4SSwapQFixerPumpPNewQSquareOutcome x c1 c2 c3 q s t
      (q ◇ (q ◇ x)) (q ◇ (q ◇ (q ◇ x))) first := by
  rcases e677_d4_s_swap_qFixerPump_qSquareOutcome h pump with
    ⟨pump, pPhase, uPhase, pPhase_lt, uPhase_lt, p_eq, u_eq,
      pPhase_fixes_q, pPhase_ne_uPhase, reduction⟩ |
    ⟨pump, pPhase, pPhase_lt, p_eq, pPhase_fixes_q, u_off_t, uFirst⟩ |
    ⟨pump, p_off_t, pFirst, uPhase, uPhase_lt, u_eq⟩ |
    ⟨pump, p_off_t, pFirst, u_off_t, uPhase, uPhase_pos, uPhase_lt, u_eq⟩ |
    ⟨pump, p_off_t, pFirst, u_off_t, u_off_p, uFirst⟩
  · exact .bothOnT pump pPhase uPhase pPhase_lt uPhase_lt p_eq u_eq
      pPhase_fixes_q pPhase_ne_uPhase reduction
  · exact .pOnT_uEscape pump pPhase pPhase_lt p_eq pPhase_fixes_q
      u_off_t uFirst
  · exact .pNew_uOnT pump p_off_t pFirst uPhase uPhase_lt u_eq
      (e677_d4_s_swap_pNew_uOnT_qSquareReduction h pump p_off_t pFirst
        uPhase uPhase_lt u_eq)
  · exact .pNew_uOnP pump p_off_t pFirst u_off_t uPhase uPhase_pos
      uPhase_lt u_eq
      (e677_d4_s_swap_pNew_uOnP_qSquareReduction h pump p_off_t pFirst
        u_off_t uPhase uPhase_pos uPhase_lt u_eq)
  · exact .pNew_uEscape pump p_off_t pFirst u_off_t u_off_p uFirst

end FiniteMagmaE677.SSwap
end
end

universe u
open FiniteMagmaE677

theorem solution
{α : Type u} [Fintype α] (op : α → α → α) (h : FiniteMagmaE677.E677 op)
(x c1 c2 c3 q s t : α)
(first : FirstReturn.D4FirstReturn op x c1 c2 c3 t 0)
(pump : SSwap.Pump op x c1 c2 c3 q s t
  (op q (op q x)) (op q (op q (op q x))) first) :
SSwap.QSquareSeed op x c1 c2 c3 q s (op q (op q x)) (op q (op q (op q x))) ∧
SSwap.QSquareOutcome op x c1 c2 c3 q s t
  (op q (op q x)) (op q (op q (op q x))) first := by
  letI : SSwap.Magma' α := ⟨op⟩
  exact ⟨SSwap.e677_d4_s_swap_qSquareSeed h pump.input pump.q_eq pump.s_eq,
    SSwap.e677_d4_s_swap_qFixerPump_pNewQSquareOutcome h pump⟩

#print axioms solution
