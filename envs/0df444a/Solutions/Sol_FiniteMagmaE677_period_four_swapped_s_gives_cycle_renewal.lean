-- Prove2me | solution 1 for FiniteMagmaE677.period_four_swapped_s_gives_cycle_renewal
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-24T08:36:58.037118+00:00
-- url     : https://prove2.me/submissions/55588a66-7a58-4198-8e82-2beec0adb8ce

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

universe u
open FiniteMagmaE677

theorem solution
{α : Type u} [Fintype α] (op : α → α → α) (h : FiniteMagmaE677.E677 op)
(x c1 c2 c3 : α)
(packet : FirstReturn.D4Distinguished op x c1 c2 c3)
(start : FirstReturn.STaggedStart op x c1 c2 c3)
(q_to_s : op x (op c2 x) = op c3 (op c2 x))
(s_to_q : op x (op c3 (op c2 x)) = op c2 x)
(fresh : FirstReturn.FreshOutsideSix x c1 c2 c3
  (op c2 x) (op c3 (op c2 x)) (op c2 (op c3 (op c2 x))))
(initial_trace : FirstReturn.D4Trace op x c1 c2 c3 (op c2 (op c3 (op c2 x))) 0)
(first : FirstReturn.D4FirstReturn op x c1 c2 c3 (op c2 (op c3 (op c2 x))) 0)
(bridge : op (op c2 (op c3 (op c2 x))) c2 = c3) :
SSwap.CycleRenewal op x c1 c2 c3 (op c2 x) (op c3 (op c2 x))
  (op c2 (op c3 (op c2 x))) first := by
  letI : SSwap.Magma' α := ⟨op⟩
  exact SSwap.e677_d4_s_swap_cycleRenewalPacket_of_published h packet start
    q_to_s s_to_q fresh initial_trace first bridge

#print axioms solution
