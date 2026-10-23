-- Prove2me | solution 1 for BNCovPack.Covering.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T23:23:58.229782+00:00
-- url     : https://prove2.me/submissions/bd440950-509b-4a03-a0ef-9113f49fb120

import Mathlib
import Definitions.Def_BNCovPack_Covering_Run

set_option autoImplicit false

namespace BNCovPackB57

open BNCovPack.Covering OnlinePrimalDual.GeneralPacking

variable {I : Type*} [Fintype I] [DecidableEq I] {m : ℕ}

lemma cardpos [Nonempty I] : (0:ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos

lemma logpos [Nonempty I] : 0 < Real.log (2 * (Fintype.card I : ℝ)) := by
  apply Real.log_pos
  have : (1:ℝ) ≤ Fintype.card I := by exact_mod_cast Fintype.card_pos
  linarith

lemma sum_update_mul (w y : Fin m → ℝ) (k : Fin m) (hy : y k = 0) (u : ℝ) :
    ∑ k', w k' * Function.update y k u k' = ∑ k', w k' * y k' + w k * u := by
  have h : ∀ k', w k' * Function.update y k u k' =
      w k' * y k' + if k' = k then w k * u else 0 := by
    intro k'
    by_cases hk : k' = k
    · subst hk; simp [hy]
    · simp [Function.update_of_ne hk, hk]
  rw [Finset.sum_congr rfl (fun k' _ => h k'), Finset.sum_add_distrib]
  simp

lemma phasePrimal_pos [Nonempty I] (inst : GeneralInstance I (Fin m)) (α : ℝ) (hα : 0 < α)
    (y : Fin m → ℝ) (i : I) : 0 < phasePrimal inst α y i := by
  unfold phasePrimal
  have hc := inst.hc_pos i
  have hn := cardpos (I := I)
  apply mul_pos _ (Real.exp_pos _)
  apply div_pos hα
  positivity

lemma atTime_x (inst : GeneralInstance I (Fin m)) (p : Phase I m) (k : Fin m)
    (hx : p.x = phasePrimal inst p.alpha p.y) (hy : p.y k = 0) (u : ℝ) (i : I) :
    (atTime inst p k u).x i =
      p.x i * Real.exp (Real.log (2 * (Fintype.card I : ℝ)) / inst.c i * inst.a i k * u) := by
  simp only [atTime, hx, phasePrimal]
  rw [sum_update_mul (inst.a i) p.y k hy u, mul_add, Real.exp_add]
  ring

lemma lim_le (f : ℝ → ℝ) (hf : Continuous f) (t c : ℝ) (ht : 0 < t)
    (h : ∀ u, 0 ≤ u → u < t → f u < c) : f t ≤ c := by
  have h1 : Filter.Tendsto f (nhdsWithin t (Set.Iio t)) (nhds (f t)) :=
    hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto h1
  filter_upwards [Ioo_mem_nhdsLT ht] with u hu
  exact (h u hu.1.le hu.2).le

lemma round_phase [Nonempty I] (inst : GeneralInstance I (Fin m)) (B : ℝ) (hB : 0 < B)
    (p : Phase I m) (k : Fin m)
    (hx : p.x = phasePrimal inst p.alpha p.y) (hyk : p.y k = 0)
    (hapos : 0 < p.alpha) (hcap : phaseCost inst p ≤ p.alpha)
    (hphase : phaseCost inst p ≤
      p.alpha / 2 + Real.log (2 * (Fintype.card I : ℝ)) / B * ∑ k', p.y k')
    (t : ℝ) (hstop : BeforeStop inst B p k t) :
    phaseCost inst (atTime inst p k t) ≤ p.alpha ∧
    phaseCost inst (atTime inst p k t) ≤
      p.alpha / 2 + Real.log (2 * (Fintype.card I : ℝ)) / B * ∑ k', (atTime inst p k t).y k' ∧
    (∀ i, p.x i ≤ (atTime inst p k t).x i) ∧ (∀ i, 0 ≤ (atTime inst p k t).x i) := by
  have hxpos : ∀ i, 0 < p.x i := fun i => by rw [hx]; exact phasePrimal_pos inst _ hapos _ i
  have hform := atTime_x inst p k hx hyk
  have hL := logpos (I := I)
  set L := Real.log (2 * (Fintype.card I : ℝ)) with hLdef
  obtain ⟨ht0, hbefore⟩ := hstop
  have hcst : ∀ u, phaseCost inst (atTime inst p k u) =
      ∑ i, inst.c i * (p.x i * Real.exp (L / inst.c i * inst.a i k * u)) := by
    intro u; simp only [phaseCost, hform]
  have hcov : ∀ u, coverage inst (atTime inst p k u) k =
      ∑ i, inst.a i k * (p.x i * Real.exp (L / inst.c i * inst.a i k * u)) := by
    intro u; simp only [coverage, hform]
  have hc1 : Continuous
      (fun u => ∑ i, inst.c i * (p.x i * Real.exp (L / inst.c i * inst.a i k * u))) := by
    fun_prop
  have hc2 : Continuous
      (fun u => ∑ i, inst.a i k * (p.x i * Real.exp (L / inst.c i * inst.a i k * u))) := by
    fun_prop
  have hc0 : (∑ i, inst.c i * (p.x i * Real.exp (L / inst.c i * inst.a i k * 0))) =
      phaseCost inst p := by
    simp [phaseCost]
  have hcovt : t * (∑ i, inst.a i k * (p.x i * Real.exp (L / inst.c i * inst.a i k * t))) ≤
      t / B := by
    rcases ht0.lt_or_eq with htp | hteq
    · have := lim_le _ hc2 t (1 / B) htp
        (fun u hu0 hut => by rw [← hcov]; exact (hbefore u hu0 hut).1)
      calc _ ≤ t * (1 / B) := mul_le_mul_of_nonneg_left this ht0
        _ = t / B := by ring
    · subst hteq; simp
  have hkey : (∑ i, inst.c i * (p.x i * Real.exp (L / inst.c i * inst.a i k * t))) -
      phaseCost inst p ≤
      L * (t * (∑ i, inst.a i k * (p.x i * Real.exp (L / inst.c i * inst.a i k * t)))) := by
    rw [← hc0, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hc := inst.hc_pos i
    have hexp : ∀ z : ℝ, Real.exp z - 1 ≤ z * Real.exp z := by
      intro z
      have h1 := Real.add_one_le_exp (-z)
      have h2 : Real.exp (-z) * Real.exp z = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos z]
    have hz : inst.c i * (L / inst.c i * inst.a i k * t) = L * inst.a i k * t := by
      field_simp
    have e := hexp (L / inst.c i * inst.a i k * t)
    have hxi := (hxpos i).le
    calc inst.c i * (p.x i * Real.exp (L / inst.c i * inst.a i k * t)) -
          inst.c i * (p.x i * Real.exp (L / inst.c i * inst.a i k * 0))
        = inst.c i * p.x i * (Real.exp (L / inst.c i * inst.a i k * t) - 1) := by
          rw [mul_zero, Real.exp_zero]; ring
      _ ≤ inst.c i * p.x i *
            ((L / inst.c i * inst.a i k * t) * Real.exp (L / inst.c i * inst.a i k * t)) :=
          mul_le_mul_of_nonneg_left e (mul_nonneg hc.le hxi)
      _ = L * (t * (inst.a i k * (p.x i * Real.exp (L / inst.c i * inst.a i k * t)))) := by
          linear_combination (p.x i * Real.exp (L / inst.c i * inst.a i k * t)) * hz
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hcst]
    rcases ht0.lt_or_eq with htp | hteq
    · exact lim_le _ hc1 t _ htp
        (fun u hu0 hut => by rw [← hcst]; exact (hbefore u hu0 hut).2)
    · subst hteq; rw [hc0]; exact hcap
  · rw [hcst]
    have hsum : ∑ k', (atTime inst p k t).y k' = ∑ k', p.y k' + t := by
      have := sum_update_mul (fun _ => (1:ℝ)) p.y k hyk t
      simp only [one_mul] at this
      exact this
    rw [hsum]
    have h4 : L * (t * (∑ i, inst.a i k * (p.x i * Real.exp (L / inst.c i * inst.a i k * t))))
        ≤ L * (t / B) := mul_le_mul_of_nonneg_left hcovt hL.le
    have h3 : L / B * (∑ k', p.y k' + t) = L / B * ∑ k', p.y k' + L * (t / B) := by ring
    rw [h3]; linarith
  · intro i; rw [hform]
    exact le_mul_of_one_le_right (hxpos i).le (Real.one_le_exp
      (mul_nonneg (mul_nonneg (div_nonneg hL.le (inst.hc_pos i).le) (inst.ha_nonneg i k)) ht0))
  · intro i; rw [hform]; exact mul_nonneg (hxpos i).le (Real.exp_pos _).le

lemma step_avail [Nonempty I] (inst : GeneralInstance I (Fin m)) (B : ℝ) (hB : 0 < B)
    (p : Phase I m) (k : Fin m)
    (hx : p.x = phasePrimal inst p.alpha p.y) (hyk : p.y k = 0)
    (hapos : 0 < p.alpha) (hcap : phaseCost inst p ≤ p.alpha)
    (hphase : phaseCost inst p ≤
      p.alpha / 2 + Real.log (2 * (Fintype.card I : ℝ)) / B * ∑ k', p.y k')
    (hposk : ∃ i, 0 < inst.a i k) :
    ∃ t, BeforeStop inst B p k t ∧ (1 / B ≤ coverage inst (atTime inst p k t) k ∨
      (phaseCost inst (atTime inst p k t) = p.alpha ∧
        coverage inst (atTime inst p k t) k < 1 / B)) := by
  have hL := logpos (I := I)
  have hxpos : ∀ i, 0 < p.x i := fun i => by rw [hx]; exact phasePrimal_pos inst _ hapos _ i
  have hform := atTime_x inst p k hx hyk
  have hc1 : Continuous (fun u => phaseCost inst (atTime inst p k u)) := by
    simp only [phaseCost, hform]; fun_prop
  have hc2 : Continuous (fun u => coverage inst (atTime inst p k u) k) := by
    simp only [coverage, hform]; fun_prop
  obtain ⟨i0, hi0⟩ := hposk
  have hx0 := hxpos i0
  have hc0 := inst.hc_pos i0
  have hu0pos : 0 < inst.c i0 /
      (B * inst.a i0 k ^ 2 * p.x i0 * Real.log (2 * (Fintype.card I : ℝ))) := by positivity
  have hcov0 : 1 / B ≤ coverage inst (atTime inst p k (inst.c i0 /
      (B * inst.a i0 k ^ 2 * p.x i0 * Real.log (2 * (Fintype.card I : ℝ))))) k := by
    simp only [coverage, hform]
    have hterm := Finset.single_le_sum (f := fun i => inst.a i k * (p.x i * Real.exp
      (Real.log (2 * (Fintype.card I : ℝ)) / inst.c i * inst.a i k * (inst.c i0 /
      (B * inst.a i0 k ^ 2 * p.x i0 * Real.log (2 * (Fintype.card I : ℝ)))))))
      (fun i _ => mul_nonneg (inst.ha_nonneg i k)
        (mul_nonneg (hxpos i).le (Real.exp_pos _).le)) (Finset.mem_univ i0)
    refine le_trans ?_ hterm
    have he := Real.add_one_le_exp (Real.log (2 * (Fintype.card I : ℝ)) / inst.c i0 *
      inst.a i0 k * (inst.c i0 /
      (B * inst.a i0 k ^ 2 * p.x i0 * Real.log (2 * (Fintype.card I : ℝ)))))
    have hval : inst.a i0 k * (p.x i0 * (Real.log (2 * (Fintype.card I : ℝ)) / inst.c i0 *
      inst.a i0 k * (inst.c i0 /
      (B * inst.a i0 k ^ 2 * p.x i0 * Real.log (2 * (Fintype.card I : ℝ)))))) = 1 / B := by
      field_simp
    have hax : 0 ≤ inst.a i0 k * p.x i0 := by positivity
    nlinarith
  let S : Set ℝ := {u | 0 ≤ u ∧ (1 / B ≤ coverage inst (atTime inst p k u) k ∨
    p.alpha ≤ phaseCost inst (atTime inst p k u))}
  have hS : IsClosed S := by
    show IsClosed ({u : ℝ | 0 ≤ u} ∩ ({u | 1 / B ≤ coverage inst (atTime inst p k u) k} ∪
      {u | p.alpha ≤ phaseCost inst (atTime inst p k u)}))
    exact (isClosed_le continuous_const continuous_id).inter
      ((isClosed_le continuous_const hc2).union (isClosed_le continuous_const hc1))
  have hne : S.Nonempty := ⟨_, hu0pos.le, Or.inl hcov0⟩
  have hbdd : BddBelow S := ⟨0, fun u hu => hu.1⟩
  have htS : sInf S ∈ S := hS.csInf_mem hne hbdd
  have hbs : BeforeStop inst B p k (sInf S) := by
    refine ⟨htS.1, fun u hu0' hut => ?_⟩
    have hnot : u ∉ S := fun huS => absurd (csInf_le hbdd huS) (not_le.mpr hut)
    simp only [S, Set.mem_setOf_eq, not_and, not_or, not_le] at hnot
    exact hnot hu0'
  refine ⟨sInf S, hbs, ?_⟩
  rcases htS.2 with h | h
  · exact Or.inl h
  · by_cases hc : 1 / B ≤ coverage inst (atTime inst p k (sInf S)) k
    · exact Or.inl hc
    · exact Or.inr ⟨le_antisymm
        (round_phase inst B hB p k hx hyk hapos hcap hphase _ hbs).1 h, not_le.mp hc⟩

lemma restart_alpha_le [Nonempty I] (inst : GeneralInstance I (Fin m)) (B : ℝ) (hB : 0 < B)
    (J : ℕ) (x'' : I → ℝ) (hx0 : ∀ i, 0 ≤ x'' i)
    (hcov'' : ∀ k : Fin m, k.val < J → 1 ≤ ∑ i, inst.a i k * x'' i)
    (p : Phase I m) (k : Fin m)
    (hx : p.x = phasePrimal inst p.alpha p.y) (hy0 : ∀ k' : Fin m, p.seen ≤ k'.val → p.y k' = 0)
    (hynn : ∀ k', 0 ≤ p.y k') (hapos : 0 < p.alpha) (hcap : phaseCost inst p ≤ p.alpha)
    (hphase : phaseCost inst p ≤
      p.alpha / 2 + Real.log (2 * (Fintype.card I : ℝ)) / B * ∑ k', p.y k')
    (hk : p.seen = k.val) (hkJ : k.val < J) (t : ℝ) (hstop : BeforeStop inst B p k t)
    (hcapeq : phaseCost inst (atTime inst p k t) = p.alpha) :
    p.alpha ≤ 2 * Real.log (2 * (Fintype.card I : ℝ)) * (∑ i, inst.c i * x'' i) / B := by
  have hL := logpos (I := I)
  have hn := cardpos (I := I)
  have hyk : p.y k = 0 := hy0 k (le_of_eq hk)
  obtain ⟨_, hph, _, hqnn⟩ := round_phase inst B hB p k hx hyk hapos hcap hphase t hstop
  have hqy : ∀ k', (atTime inst p k t).y k' = Function.update p.y k t k' := fun _ => rfl
  have hqynn : ∀ k', 0 ≤ (atTime inst p k t).y k' := by
    intro k'; rw [hqy]
    by_cases h : k' = k
    · subst h; simp [hstop.1]
    · rw [Function.update_of_ne h]; exact hynn k'
  have hqyJ : ∀ k' : Fin m, J ≤ k'.val → (atTime inst p k t).y k' = 0 := by
    intro k' hk'
    have hne : k' ≠ k := by intro h; subst h; omega
    rw [hqy, Function.update_of_ne hne]; exact hy0 k' (by omega)
  set L := Real.log (2 * (Fintype.card I : ℝ)) with hLd
  have hfeas : ∀ i, ∑ k', inst.a i k' * (atTime inst p k t).y k' ≤ inst.c i := by
    intro i
    have hc := inst.hc_pos i
    have h1 : inst.c i * (atTime inst p k t).x i ≤ p.alpha := by
      rw [← hcapeq]; unfold phaseCost
      exact Finset.single_le_sum (f := fun j => inst.c j * (atTime inst p k t).x j)
        (fun j _ => mul_nonneg (inst.hc_pos j).le (hqnn j)) (Finset.mem_univ i)
    have h2 : (atTime inst p k t).x i = phasePrimal inst p.alpha (atTime inst p k t).y i := rfl
    rw [h2, phasePrimal] at h1
    set Sm := ∑ k', inst.a i k' * (atTime inst p k t).y k' with hSm
    have h4 : inst.c i * (p.alpha / (2 * (Fintype.card I : ℝ) * inst.c i) *
        Real.exp (L / inst.c i * Sm)) =
        p.alpha * Real.exp (L / inst.c i * Sm) / (2 * (Fintype.card I : ℝ)) := by
      field_simp
    rw [h4, div_le_iff₀ (by positivity)] at h1
    have h5 : Real.exp (L / inst.c i * Sm) ≤ 2 * (Fintype.card I : ℝ) :=
      le_of_mul_le_mul_left h1 hapos
    have h6e : Real.exp L = 2 * (Fintype.card I : ℝ) := Real.exp_log (by positivity)
    have h6 : L / inst.c i * Sm ≤ L := Real.exp_le_exp.mp (h5.trans_eq h6e.symm)
    rw [div_mul_eq_mul_div, div_le_iff₀ hc] at h6
    exact le_of_mul_le_mul_left h6 hL
  have hY : ∑ k', (atTime inst p k t).y k' ≤ ∑ i, inst.c i * x'' i := by
    calc ∑ k', (atTime inst p k t).y k'
        ≤ ∑ k', (atTime inst p k t).y k' * ∑ i, inst.a i k' * x'' i := by
          apply Finset.sum_le_sum; intro k' _
          by_cases hk' : k'.val < J
          · exact le_mul_of_one_le_right (hqynn k') (hcov'' k' hk')
          · rw [hqyJ k' (by omega)]; simp
      _ = ∑ i, x'' i * ∑ k', inst.a i k' * (atTime inst p k t).y k' := by
          simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro k' _; ring
      _ ≤ ∑ i, x'' i * inst.c i :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hfeas i) (hx0 i))
      _ = ∑ i, inst.c i * x'' i := Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have hLB : 0 ≤ L / B := div_nonneg hL.le hB.le
  have h7 := mul_le_mul_of_nonneg_left hY hLB
  rw [hcapeq] at hph
  have h8 : 2 * L * (∑ i, inst.c i * x'' i) / B = 2 * (L / B * ∑ i, inst.c i * x'' i) := by ring
  rw [h8]; linarith

structure PhInv (inst : GeneralInstance I (Fin m)) (B : ℝ) (hm : 0 < m) (OPT : ℝ)
    (s : State I m) : Prop where
  hx : s.current.x = phasePrimal inst s.current.alpha s.current.y
  hy0 : ∀ k : Fin m, s.current.seen ≤ k.val → s.current.y k = 0
  hynn : ∀ k, 0 ≤ s.current.y k
  hseen : s.current.seen ≤ s.arrived
  hcap : phaseCost inst s.current ≤ s.current.alpha
  hphase : phaseCost inst s.current ≤
    s.current.alpha / 2 + Real.log (2 * (Fintype.card I : ℝ)) / B * ∑ k, s.current.y k
  hcovd : ∀ k : Fin m, k.val < s.current.seen → 1 / B ≤ coverage inst s.current k
  hapos : 0 < s.current.alpha
  hfin : (s.finished.map (phaseCost inst)).sum ≤ s.current.alpha
  hgrow : (s.finished = [] ∧ s.current.alpha = firstAlpha inst B hm) ∨
    s.current.alpha ≤ 4 * Real.log (2 * (Fintype.card I : ℝ)) * OPT / B
  hfinnn : ∀ p ∈ s.finished, ∀ i, 0 ≤ p.x i

lemma initialPhase_x (inst : GeneralInstance I (Fin m)) (α : ℝ) :
    (initialPhase inst α).x = phasePrimal inst α (initialPhase inst α).y := by
  funext i; simp [initialPhase, phasePrimal]

lemma initCost [Nonempty I] (inst : GeneralInstance I (Fin m)) (α : ℝ) :
    phaseCost inst (initialPhase inst α) = α / 2 := by
  have hn := cardpos (I := I)
  unfold phaseCost initialPhase
  simp only
  have h : ∀ i, inst.c i * (α / (2 * (Fintype.card I : ℝ) * inst.c i)) =
      α / (2 * Fintype.card I) := by
    intro i; have := inst.hc_pos i; field_simp
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

lemma step_arrived {inst : GeneralInstance I (Fin m)} {B : ℝ} {s s' : State I m}
    (h : Step inst B s s') : s.arrived ≤ s'.arrived := by
  cases h with
  | arrive _ _ => show s.arrived ≤ s.arrived + 1; omega
  | cover _ _ _ _ _ _ => exact le_rfl
  | restart _ _ _ _ _ _ _ => exact le_rfl

lemma inv_step [Nonempty I] (inst : GeneralInstance I (Fin m)) (B : ℝ) (hB : 0 < B)
    (hm : 0 < m) (J : ℕ) (x'' : I → ℝ) (hx0 : ∀ i, 0 ≤ x'' i)
    (hcov'' : ∀ k : Fin m, k.val < J → 1 ≤ ∑ i, inst.a i k * x'' i)
    {s s' : State I m} (hst : Step inst B s s') (hJ : s'.arrived ≤ J)
    (hs : PhInv inst B hm (∑ i, inst.c i * x'' i) s) :
    PhInv inst B hm (∑ i, inst.c i * x'' i) s' := by
  cases hst with
  | arrive hready hmore =>
    have := hs.hseen
    exact ⟨hs.hx, hs.hy0, hs.hynn, by show s.current.seen ≤ s.arrived + 1; omega, hs.hcap,
      hs.hphase, hs.hcovd, hs.hapos, hs.hfin, hs.hgrow, hs.hfinnn⟩
  | cover k t hk hknown hstop hcover =>
    have hyk : s.current.y k = 0 := hs.hy0 k (le_of_eq hk)
    obtain ⟨hcq, hpq, hmono, _⟩ :=
      round_phase inst B hB s.current k hs.hx hyk hs.hapos hs.hcap hs.hphase t hstop
    refine ⟨rfl, ?_, ?_, ?_, hcq, hpq, ?_, hs.hapos, hs.hfin, hs.hgrow, hs.hfinnn⟩
    · intro k' hk'
      have hk'' : k.val + 1 ≤ k'.val := hk'
      have hne : k' ≠ k := by intro h; subst h; omega
      show Function.update s.current.y k t k' = 0
      rw [Function.update_of_ne hne]; exact hs.hy0 k' (by omega)
    · intro k'
      show 0 ≤ Function.update s.current.y k t k'
      by_cases h : k' = k
      · subst h; simp [hstop.1]
      · rw [Function.update_of_ne h]; exact hs.hynn k'
    · show k.val + 1 ≤ s.arrived; omega
    · intro k' hk'
      have hk'' : k'.val < k.val + 1 := hk'
      show 1 / B ≤ coverage inst (atTime inst s.current k t) k'
      rcases Nat.lt_or_ge k'.val k.val with hlt | hge
      · refine (hs.hcovd k' (by omega)).trans ?_
        exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hmono i) (inst.ha_nonneg i k'))
      · have : k' = k := Fin.ext (by omega)
        subst this; exact hcover
  | restart k t hk hknown hstop hcapeq hunc =>
    have hJ' : s.arrived ≤ J := hJ
    have hαle := restart_alpha_le inst B hB J x'' hx0 hcov'' s.current k hs.hx hs.hy0 hs.hynn
      hs.hapos hs.hcap hs.hphase hk (by omega) t hstop hcapeq
    obtain ⟨_, _, _, hqnn⟩ :=
      round_phase inst B hB s.current k hs.hx (hs.hy0 k (le_of_eq hk)) hs.hapos hs.hcap
        hs.hphase t hstop
    have hα := hs.hapos
    have hfin := hs.hfin
    refine ⟨initialPhase_x inst _, fun _ _ => rfl, fun _ => le_rfl, Nat.zero_le _, ?_, ?_,
      fun k' hk' => absurd hk' (Nat.not_lt_zero _), ?_, ?_, ?_, ?_⟩
    · show phaseCost inst (initialPhase inst (2 * s.current.alpha)) ≤ 2 * s.current.alpha
      rw [initCost]; linarith
    · show phaseCost inst (initialPhase inst (2 * s.current.alpha)) ≤
        2 * s.current.alpha / 2 + Real.log (2 * (Fintype.card I : ℝ)) / B *
          ∑ k, (fun _ => (0:ℝ)) k
      rw [initCost]; simp
    · show 0 < 2 * s.current.alpha; linarith
    · show ((s.finished ++ [atTime inst s.current k t]).map (phaseCost inst)).sum ≤
        2 * s.current.alpha
      rw [List.map_append, List.sum_append]; simp only [List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero]
      rw [hcapeq]; linarith
    · right
      show 2 * s.current.alpha ≤
        4 * Real.log (2 * (Fintype.card I : ℝ)) * (∑ i, inst.c i * x'' i) / B
      have h9 : 4 * Real.log (2 * (Fintype.card I : ℝ)) * (∑ i, inst.c i * x'' i) / B =
        2 * (2 * Real.log (2 * (Fintype.card I : ℝ)) * (∑ i, inst.c i * x'' i) / B) := by ring
      rw [h9]; linarith
    · intro p hp i
      rcases List.mem_append.mp hp with hp | hp
      · exact hs.hfinnn p hp i
      · rw [List.mem_singleton] at hp; subst hp; exact hqnn i

lemma firstAlpha_facts (inst : GeneralInstance I (Fin m)) (B : ℝ) (hB : 0 < B) (hm : 0 < m)
    (h0 : ∃ i, 0 < inst.a i ⟨0, hm⟩) :
    0 < firstAlpha inst B hm ∧ ∀ x'' : I → ℝ, (∀ i, 0 ≤ x'' i) →
      1 ≤ ∑ i, inst.a i ⟨0, hm⟩ * x'' i →
      firstAlpha inst B hm * B ≤ ∑ i, inst.c i * x'' i := by
  set T : Set ℝ := {z : ℝ | ∃ i : I, 0 < inst.a i ⟨0, hm⟩ ∧ z = inst.c i / inst.a i ⟨0, hm⟩}
    with hT
  have hTne : T.Nonempty := by obtain ⟨i, hi⟩ := h0; exact ⟨_, i, hi, rfl⟩
  have hTfin : T.Finite := (Set.finite_range (fun i : I => inst.c i / inst.a i ⟨0, hm⟩)).subset
    (by rintro z ⟨i, _, rfl⟩; exact ⟨i, rfl⟩)
  have hTbdd : BddBelow T := ⟨0, by rintro z ⟨i, hi, rfl⟩; exact (div_pos (inst.hc_pos i) hi).le⟩
  have hmem := hTne.csInf_mem hTfin
  have hpos : 0 < sInf T := by
    obtain ⟨i, hi, hz⟩ := hmem; rw [hz]; exact div_pos (inst.hc_pos i) hi
  have hfa : firstAlpha inst B hm = (1 / B) * sInf T := rfl
  refine ⟨by rw [hfa]; positivity, ?_⟩
  intro x'' hx0 hcov
  rw [hfa]
  have hB' : (1 / B) * sInf T * B = sInf T := by field_simp
  rw [hB']
  calc sInf T ≤ sInf T * ∑ i, inst.a i ⟨0, hm⟩ * x'' i := le_mul_of_one_le_right hpos.le hcov
    _ = ∑ i, sInf T * (inst.a i ⟨0, hm⟩ * x'' i) := by rw [Finset.mul_sum]
    _ ≤ ∑ i, inst.c i * x'' i := by
      apply Finset.sum_le_sum; intro i _
      rcases (inst.ha_nonneg i ⟨0, hm⟩).lt_or_eq with hi | hi
      · have h1 : sInf T ≤ inst.c i / inst.a i ⟨0, hm⟩ := csInf_le hTbdd ⟨i, hi, rfl⟩
        rw [le_div_iff₀ hi] at h1
        calc sInf T * (inst.a i ⟨0, hm⟩ * x'' i) = (sInf T * inst.a i ⟨0, hm⟩) * x'' i := by ring
          _ ≤ inst.c i * x'' i := mul_le_mul_of_nonneg_right h1 (hx0 i)
      · rw [← hi, zero_mul, mul_zero]; exact mul_nonneg (inst.hc_pos i).le (hx0 i)

lemma inv_first [Nonempty I] (inst : GeneralInstance I (Fin m)) (B : ℝ) (hB : 0 < B)
    (hm : 0 < m) (OPT : ℝ) (h0 : ∃ i, 0 < inst.a i ⟨0, hm⟩) :
    PhInv inst B hm OPT (firstState inst B hm) := by
  have hα := (firstAlpha_facts inst B hB hm h0).1
  refine ⟨initialPhase_x inst _, fun _ _ => rfl, fun _ => le_rfl, Nat.zero_le _, ?_, ?_,
    fun k' hk' => absurd hk' (Nat.not_lt_zero _), hα, ?_, Or.inl ⟨rfl, rfl⟩, ?_⟩
  · show phaseCost inst (initialPhase inst (firstAlpha inst B hm)) ≤ firstAlpha inst B hm
    rw [initCost]; linarith
  · show phaseCost inst (initialPhase inst (firstAlpha inst B hm)) ≤
      firstAlpha inst B hm / 2 + Real.log (2 * (Fintype.card I : ℝ)) / B *
        ∑ k, (fun _ => (0:ℝ)) k
    rw [initCost]; simp
  · show (([] : List (Phase I m)).map (phaseCost inst)).sum ≤ firstAlpha inst B hm
    simp; exact hα.le
  · intro p hp; exact absurd hp (List.not_mem_nil)

lemma run_inv [Nonempty I] (inst : GeneralInstance I (Fin m)) (B : ℝ) (hB : 0 < B)
    (hm : 0 < m) (J : ℕ) (x'' : I → ℝ) (hx0 : ∀ i, 0 ≤ x'' i)
    (hcov'' : ∀ k : Fin m, k.val < J → 1 ≤ ∑ i, inst.a i k * x'' i)
    (h0 : ∃ i, 0 < inst.a i ⟨0, hm⟩) {s : State I m}
    (h : Relation.ReflTransGen (Step inst B) (firstState inst B hm) s) :
    s.arrived ≤ J → PhInv inst B hm (∑ i, inst.c i * x'' i) s := by
  induction h with
  | refl => intro _; exact inv_first inst B hB hm _ h0
  | tail _ hbc ih =>
    intro hJc
    exact inv_step inst B hB hm J x'' hx0 hcov'' hbc hJc (ih (le_trans (step_arrived hbc) hJc))

lemma inner [Nonempty I] (inst : GeneralInstance I (Fin m)) (B : ℝ) (hB : 0 < B)
    (hm : 0 < m) (J : ℕ) (hJm : J ≤ m)
    (hpositive : ∀ k : Fin m, k.val < J → ∃ i : I, 0 < inst.a i k)
    (x'' : I → ℝ) (hx0 : ∀ i, 0 ≤ x'' i)
    (hcov'' : ∀ k : Fin m, k.val < J → 1 ≤ ∑ i, inst.a i k * x'' i) (α : ℝ)
    (hnext : α ≤ 2 * Real.log (2 * (Fintype.card I : ℝ)) * (∑ i, inst.c i * x'' i) / B →
      ∀ s : State I m, s.arrived ≤ J → PhInv inst B hm (∑ i, inst.c i * x'' i) s →
        s.current.alpha = 2 * α →
        ∃ s', Relation.ReflTransGen (Step inst B) s s' ∧ s'.arrived = J ∧
          s'.current.seen = J) :
    ∀ d : ℕ, ∀ s : State I m, (J - s.arrived) + (J - s.current.seen) = d → s.arrived ≤ J →
      PhInv inst B hm (∑ i, inst.c i * x'' i) s → s.current.alpha = α →
        ∃ s', Relation.ReflTransGen (Step inst B) s s' ∧ s'.arrived = J ∧
          s'.current.seen = J := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro s hd hJ hs hα
  have hseen := hs.hseen
  have cont : ∀ s1, Step inst B s s1 → s1.arrived ≤ J →
      PhInv inst B hm (∑ i, inst.c i * x'' i) s1 → s1.current.alpha = α →
      (J - s1.arrived) + (J - s1.current.seen) < d → ∃ s', Relation.ReflTransGen (Step inst B) s s' ∧ s'.arrived = J ∧ s'.current.seen = J := by
    intro s1 hst hJ1 hs1 hα1 hlt1
    obtain ⟨s', h1, h2, h3⟩ := ih _ hlt1 s1 rfl hJ1 hs1 hα1
    exact ⟨s', Relation.ReflTransGen.head hst h1, h2, h3⟩
  rcases Nat.lt_or_ge s.current.seen s.arrived with hlt | hge
  · have hseenm : s.current.seen < m := by omega
    let k : Fin m := ⟨s.current.seen, hseenm⟩
    have hk : s.current.seen = k.val := rfl
    have hyk : s.current.y k = 0 := hs.hy0 k le_rfl
    obtain ⟨t, hstop, hres⟩ := step_avail inst B hB s.current k hs.hx hyk hs.hapos hs.hcap
      hs.hphase (hpositive k (by omega))
    rcases hres with hcover | ⟨hcapeq, hunc⟩
    · have hst := Step.cover s k t hk hlt hstop hcover
      have hs1 := inv_step inst B hB hm J x'' hx0 hcov'' hst hJ hs
      exact cont _ hst hJ hs1 hα (by show J - s.arrived + (J - (k.val + 1)) < d; omega)
    · have hst := Step.restart s k t hk hlt hstop hcapeq hunc
      have hs1 := inv_step inst B hB hm J x'' hx0 hcov'' hst hJ hs
      have hαle := restart_alpha_le inst B hB J x'' hx0 hcov'' s.current k hs.hx hs.hy0
        hs.hynn hs.hapos hs.hcap hs.hphase hk (by omega) t hstop hcapeq
      have key : ∀ s1, Step inst B s s1 → s1.arrived ≤ J →
          PhInv inst B hm (∑ i, inst.c i * x'' i) s1 → s1.current.alpha = 2 * α → ∃ s', Relation.ReflTransGen (Step inst B) s s' ∧ s'.arrived = J ∧ s'.current.seen = J := by
        intro s1 hst1 hJ1 hs1' hα1
        obtain ⟨s', h1, h2, h3⟩ := hnext (by rw [← hα]; exact hαle) s1 hJ1 hs1' hα1
        exact ⟨s', Relation.ReflTransGen.head hst1 h1, h2, h3⟩
      exact key _ hst hJ hs1 (by show 2 * s.current.alpha = 2 * α; rw [hα])
  · have heq : s.current.seen = s.arrived := le_antisymm hseen hge
    rcases Nat.lt_or_ge s.arrived J with haJ | haJ
    · have hst := Step.arrive (inst := inst) (B := B) s heq (by omega)
      have hJ1 : s.arrived + 1 ≤ J := by omega
      have hs1 := inv_step inst B hB hm J x'' hx0 hcov'' hst hJ1 hs
      exact cont _ hst hJ1 hs1 hα
        (by show J - (s.arrived + 1) + (J - s.current.seen) < d; omega)
    · exact ⟨s, Relation.ReflTransGen.refl, by omega, by omega⟩

lemma outer [Nonempty I] (inst : GeneralInstance I (Fin m)) (B : ℝ) (hB : 0 < B)
    (hm : 0 < m) (J : ℕ) (hJm : J ≤ m)
    (hpositive : ∀ k : Fin m, k.val < J → ∃ i : I, 0 < inst.a i k)
    (x'' : I → ℝ) (hx0 : ∀ i, 0 ≤ x'' i)
    (hcov'' : ∀ k : Fin m, k.val < J → 1 ≤ ∑ i, inst.a i k * x'' i) :
    ∀ n : ℕ, ∀ s : State I m, s.arrived ≤ J → PhInv inst B hm (∑ i, inst.c i * x'' i) s →
      2 * Real.log (2 * (Fintype.card I : ℝ)) * (∑ i, inst.c i * x'' i) / B <
        2 ^ n * s.current.alpha →
      ∃ s', Relation.ReflTransGen (Step inst B) s s' ∧ s'.arrived = J ∧
        s'.current.seen = J := by
  intro n
  induction n with
  | zero =>
    intro s hJ hs hlt
    rw [pow_zero, one_mul] at hlt
    exact inner inst B hB hm J hJm hpositive x'' hx0 hcov'' s.current.alpha
      (fun h => absurd h (not_le.mpr hlt)) _ s rfl hJ hs rfl
  | succ n ih =>
    intro s hJ hs hlt
    exact inner inst B hB hm J hJm hpositive x'' hx0 hcov'' s.current.alpha
      (fun _ s' hJ' hs' hα' => ih s' hJ' hs' (by rw [hα']; rw [pow_succ] at hlt; linarith))
      _ s rfl hJ hs rfl

lemma foldl_max_ge (i : I) : ∀ (l : List (Phase I m)) (v : ℝ),
    v ≤ l.foldl (fun v p => max v (p.x i)) v
  | [], v => le_refl v
  | p :: l, v => by
    simp only [List.foldl_cons]
    exact (le_max_left v (p.x i)).trans (foldl_max_ge i l _)

lemma foldl_max_le (i : I) : ∀ (l : List (Phase I m)) (v : ℝ), 0 ≤ v →
    (∀ p ∈ l, 0 ≤ p.x i) →
    l.foldl (fun v p => max v (p.x i)) v ≤ v + (l.map (fun p => p.x i)).sum
  | [], v, _, _ => by simp
  | p :: l, v, hv, h => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    have h2 : 0 ≤ p.x i := h p (by simp)
    have h1 := foldl_max_le i l (max v (p.x i)) (le_max_of_le_left hv)
      (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have h3 : max v (p.x i) ≤ v + p.x i := max_le (by linarith) (by linarith)
    linarith

lemma sum_list_swap (inst : GeneralInstance I (Fin m)) (l : List (Phase I m)) :
    ∑ i, inst.c i * (l.map (fun p => p.x i)).sum = (l.map (phaseCost inst)).sum := by
  induction l with
  | nil => simp
  | cons p l ih =>
    rw [List.map_cons, List.sum_cons, ← ih]
    simp only [List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib]
    rfl

end BNCovPackB57

open BNCovPack.Covering OnlinePrimalDual.GeneralPacking in
theorem solution {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {m : ℕ} (inst : GeneralInstance I (Fin m)) (B : ℝ) (hB : 0 < B)
    (hm : 0 < m) (J : ℕ) (hJ : 1 ≤ J ∧ J ≤ m)
    (hpositive : ∀ k : Fin m, k.val < J → ∃ i : I, 0 < inst.a i k) :
    (∃ s : State I m, Run inst B hm J s) ∧
    ∀ s : State I m, Run inst B hm J s →
      (∀ k : Fin m, k.val < J →
        1 / B ≤ ∑ i : I, inst.a i k * output s i) ∧
      (∀ x'' : I → ℝ, (∀ i, 0 ≤ x'' i) →
        (∀ k : Fin m, k.val < J → 1 ≤ ∑ i : I, inst.a i k * x'' i) →
        (∑ i : I, inst.c i * output s i) ≤
          (8 * Real.log (2 * (Fintype.card I : ℝ)) / B) *
            ∑ i : I, inst.c i * x'' i) := by
  have h0 : ∃ i, 0 < inst.a i ⟨0, hm⟩ := hpositive ⟨0, hm⟩ (by show 0 < J; omega)
  have hL := BNCovPackB57.logpos (I := I)
  -- a comparator covering every arrived constraint
  have hA : ∀ k : Fin m, 0 ≤ ∑ i, inst.a i k :=
    fun k => Finset.sum_nonneg (fun i _ => inst.ha_nonneg i k)
  have hM : 0 ≤ ∑ k : Fin m, 1 / (∑ i, inst.a i k) :=
    Finset.sum_nonneg (fun k _ => by have := hA k; positivity)
  have hx0 : ∀ _i : I, 0 ≤ (fun _ : I => ∑ k : Fin m, 1 / (∑ i, inst.a i k)) _i := fun _ => hM
  have hcov0 : ∀ k : Fin m, k.val < J →
      1 ≤ ∑ i, inst.a i k * (fun _ : I => ∑ k : Fin m, 1 / (∑ i, inst.a i k)) i := by
    intro k hk
    obtain ⟨i, hi⟩ := hpositive k hk
    have hApos : 0 < ∑ i, inst.a i k := lt_of_lt_of_le hi
      (Finset.single_le_sum (f := fun j => inst.a j k) (fun j _ => inst.ha_nonneg j k)
        (Finset.mem_univ i))
    have h1 : 1 / (∑ i, inst.a i k) ≤ ∑ k : Fin m, 1 / (∑ i, inst.a i k) :=
      Finset.single_le_sum (f := fun k => 1 / ∑ i, inst.a i k)
        (fun k _ => by have := hA k; positivity) (Finset.mem_univ k)
    show 1 ≤ ∑ i, inst.a i k * ∑ k : Fin m, 1 / (∑ i, inst.a i k)
    rw [← Finset.sum_mul]
    calc (1:ℝ) = (∑ i, inst.a i k) * (1 / ∑ i, inst.a i k) := by field_simp
      _ ≤ (∑ i, inst.a i k) * ∑ k : Fin m, 1 / (∑ i, inst.a i k) :=
          mul_le_mul_of_nonneg_left h1 hApos.le
  refine ⟨?_, ?_⟩
  · have hα1 := (BNCovPackB57.firstAlpha_facts inst B hB hm h0).1
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt
      (2 * Real.log (2 * (Fintype.card I : ℝ)) *
        (∑ i, inst.c i * (fun _ : I => ∑ k : Fin m, 1 / (∑ i, inst.a i k)) i) / B /
          firstAlpha inst B hm) (by norm_num : (1:ℝ) < 2)
    rw [div_lt_iff₀ hα1] at hn
    obtain ⟨s', h1, h2, h3⟩ := BNCovPackB57.outer inst B hB hm J hJ.2 hpositive _ hx0 hcov0 n
      (firstState inst B hm) (by show 1 ≤ J; omega) (BNCovPackB57.inv_first inst B hB hm _ h0) hn
    exact ⟨s', h1, h2, h3⟩
  · intro s hrun
    obtain ⟨hrtg, hsa, hss⟩ := hrun
    refine ⟨?_, ?_⟩
    · intro k hk
      have hs := BNCovPackB57.run_inv inst B hB hm J _ hx0 hcov0 h0 hrtg (le_of_eq hsa)
      have hcv := hs.hcovd k (by rw [hss]; exact hk)
      refine hcv.trans ?_
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
        (BNCovPackB57.foldl_max_ge i s.finished (s.current.x i)) (inst.ha_nonneg i k))
    · intro x'' hx'' hcov''
      have hs := BNCovPackB57.run_inv inst B hB hm J x'' hx'' hcov'' h0 hrtg (le_of_eq hsa)
      have hcur : ∀ i, 0 ≤ s.current.x i := fun i => by
        rw [hs.hx]; exact (BNCovPackB57.phasePrimal_pos inst _ hs.hapos _ i).le
      have hOPT : 0 ≤ ∑ i, inst.c i * x'' i :=
        Finset.sum_nonneg (fun i _ => mul_nonneg (inst.hc_pos i).le (hx'' i))
      have h1 : ∑ i, inst.c i * output s i ≤
          phaseCost inst s.current + (s.finished.map (phaseCost inst)).sum := by
        calc ∑ i, inst.c i * output s i
            ≤ ∑ i, inst.c i * (s.current.x i + (s.finished.map (fun p => p.x i)).sum) :=
              Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
                (BNCovPackB57.foldl_max_le i s.finished (s.current.x i) (hcur i)
                  (fun p hp => hs.hfinnn p hp i)) (inst.hc_pos i).le)
          _ = phaseCost inst s.current +
                ∑ i, inst.c i * (s.finished.map (fun p => p.x i)).sum := by
              simp only [mul_add, Finset.sum_add_distrib]; rfl
          _ = phaseCost inst s.current + (s.finished.map (phaseCost inst)).sum := by
              rw [BNCovPackB57.sum_list_swap]
      have hcap := hs.hcap
      have hfin := hs.hfin
      have h8 : 1 ≤ 8 * Real.log (2 * (Fintype.card I : ℝ)) := by
        have hl2 : Real.log 2 ≤ Real.log (2 * (Fintype.card I : ℝ)) := by
          apply Real.log_le_log (by norm_num)
          have : (1:ℝ) ≤ Fintype.card I := by exact_mod_cast Fintype.card_pos
          linarith
        have := Real.log_two_gt_d9
        linarith
      rcases hs.hgrow with ⟨hnil, hαeq⟩ | hle
      · rw [hnil] at h1
        simp only [List.map_nil, List.sum_nil, add_zero] at h1
        have hfa := (BNCovPackB57.firstAlpha_facts inst B hB hm h0).2 x'' hx'' (hcov'' ⟨0, hm⟩
          (by show 0 < J; omega))
        have hfa' : firstAlpha inst B hm ≤ (∑ i, inst.c i * x'' i) / B := by
          rw [le_div_iff₀ hB]; exact hfa
        have h9 : (∑ i, inst.c i * x'' i) / B ≤
            8 * Real.log (2 * (Fintype.card I : ℝ)) / B * ∑ i, inst.c i * x'' i := by
          rw [show 8 * Real.log (2 * (Fintype.card I : ℝ)) / B * ∑ i, inst.c i * x'' i =
            (8 * Real.log (2 * (Fintype.card I : ℝ))) * ((∑ i, inst.c i * x'' i) / B) by ring]
          exact le_mul_of_one_le_left (div_nonneg hOPT hB.le) h8
        rw [hαeq] at hcap
        linarith
      · have h9 : 8 * Real.log (2 * (Fintype.card I : ℝ)) / B * ∑ i, inst.c i * x'' i =
            2 * (4 * Real.log (2 * (Fintype.card I : ℝ)) * (∑ i, inst.c i * x'' i) / B) := by
          ring
        rw [h9]; linarith
