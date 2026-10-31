-- Prove2me | solution 1 for FMLPricing.BranchBound.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T16:08:29.157885+00:00
-- url     : https://prove2.me/submissions/b4c5e099-3e06-4f2e-a45e-7fdf1c2ff1f0

import Mathlib
import Definitions.Def_FMLPricing_BranchBound_Model

open FMLPricing.BranchBound

namespace FMLAlg

variable {m n : ℕ} (I : FML m n)

lemma denom_pos (c : Fin m) (p : Fin n → ℝ) : 0 < denom I c p := by
  unfold denom; positivity

lemma q0_pos (p : Fin n → ℝ) (c : Fin m) : 0 < q0 I p c := by
  unfold q0; exact one_div_pos.mpr (denom_pos I c p)

lemma q0_mono (hI : Standing I) {p p' : Fin n → ℝ} (h : p ≤ p') (c : Fin m) :
    q0 I p c ≤ q0 I p' c := by
  unfold q0
  apply one_div_le_one_div_of_le (denom_pos I c p')
  unfold denom
  refine (add_le_add_iff_left 1).mpr (Finset.sum_le_sum fun j _ => ?_)
  exact Real.exp_le_exp.mpr (by nlinarith [hI.b_pos j, h j])

lemma Xset_bounds (hI : Standing I) {x : Fin m → ℝ} (hx : x ∈ Xset I) (c : Fin m) :
    q0 I (pLo I) c ≤ x c ∧ x c ≤ q0 I (pHi I) c := by
  obtain ⟨p, hp, rfl⟩ := hx
  exact ⟨q0_mono I hI hp.1 c, q0_mono I hI hp.2 c⟩

lemma s_mul_zOf (c : Fin m) (j : Fin n) (p : Fin n → ℝ) :
    s I c j * zOf I p j = Real.exp (I.a c j - I.b j * p j) := by
  unfold s zOf; rw [← Real.exp_add]; ring_nf

lemma q0_eq (c : Fin m) (p : Fin n → ℝ) :
    q0 I p c = 1 / (1 + ∑ j, s I c j * zOf I p j) := by
  unfold q0 denom; simp only [s_mul_zOf]

lemma sum_eq_of_q0 (c : Fin m) (p : Fin n → ℝ) :
    ∑ j, s I c j * zOf I p j = 1 / q0 I p c - 1 := by
  rw [q0_eq, one_div_one_div]; ring

lemma zOf_priceOf (hI : Standing I) {z : Fin n → ℝ} (hz : ∀ j, 0 < z j) :
    zOf I (priceOf I z) = z := by
  funext j
  unfold zOf priceOf
  rw [show -(-(I.b j)⁻¹ * Real.log (z j)) * I.b j = Real.log (z j) by
    field_simp [(hI.b_pos j).ne']]
  exact Real.exp_log (hz j)

lemma zLo_pos (j : Fin n) : 0 < zLo I j := Real.exp_pos _

lemma zOf_mem (hI : Standing I) {p : Fin n → ℝ} (hp : p ∈ priceBox I) :
    zOf I p ∈ Set.Icc (zLo I) (zHi I) :=
  ⟨fun j => Real.exp_le_exp.mpr (by nlinarith [hp.2 j, hI.b_pos j]),
   fun j => Real.exp_le_exp.mpr (by nlinarith [hp.1 j, hI.b_pos j])⟩

lemma priceOf_mem (hI : Standing I) {z : Fin n → ℝ} (hz : z ∈ Set.Icc (zLo I) (zHi I)) :
    priceOf I z ∈ priceBox I := by
  have hpos : ∀ j, 0 < z j := fun j => (zLo_pos I j).trans_le (hz.1 j)
  have h := zOf_priceOf I hI hpos
  constructor <;> intro j
  · have h2 := hz.2 j
    rw [← h] at h2
    unfold zOf zHi at h2
    have := Real.exp_le_exp.mp h2
    nlinarith [hI.b_pos j]
  · have h2 := hz.1 j
    rw [← h] at h2
    unfold zOf zLo at h2
    have := Real.exp_le_exp.mp h2
    nlinarith [hI.b_pos j]

lemma mu_eq {t : ℝ} (ht : 0 < t) : (1 - t) / t = 1 / t - 1 := by
  field_simp

lemma mu_anti {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : (1 - b) / b ≤ (1 - a) / a := by
  rw [mu_eq (ha.trans_le hab), mu_eq ha]
  have := one_div_le_one_div_of_le ha hab
  linarith

lemma xLo_pos (x : Fin m → ℝ) (r : ℝ) (c : Fin m) : 0 < xLo I x r c :=
  (q0_pos I _ c).trans_le (le_max_right _ _)

lemma xHi_pos {x : Fin m → ℝ} {r : ℝ} (hx : ∀ c, 0 < x c) (hr : 0 < r) (c : Fin m) :
    0 < xHi I x r c :=
  lt_min (by linarith [hx c]) (q0_pos I _ c)

/-- Every feasible point of `LP(x, r)` gives `χ(x, δ⁺, δ⁻) ∈ R(x, r) ∩ X`. -/
lemma chi_mem (hI : Standing I) {x : Fin m → ℝ} (hx : ∀ c, 0 < x c) {r : ℝ} (hr : 0 < r)
    {v : LPVars m n} (hv : LPFeasibleAt I x r v) :
    chi x v.δp v.δm ∈ Rbox I x r ∩ Xset I := by
  obtain ⟨h1, -, h3, h4, h5, -⟩ := hv
  have hzpos : ∀ j, 0 < v.z j := fun j => (zLo_pos I j).trans_le (h5 j).1
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hI.n_pos⟩, Finset.mem_univ _⟩
  have hy : ∀ c, 0 < ∑ j, s I c j * v.z j := fun c =>
    Finset.sum_pos (fun j _ => mul_pos (Real.exp_pos _) (hzpos j)) hne
  have hchi : ∀ c, chi x v.δp v.δm c = 1 / (1 + ∑ j, s I c j * v.z j) := by
    intro c
    have e : v.δm c - v.δp c = (∑ j, s I c j * v.z j) - (1 - x c) / x c := by
      have := h1 c; unfold mu at this; linarith
    unfold chi
    rw [e]
    have hxc := (hx c).ne'
    have hyc := hy c
    rw [div_eq_div_iff (by field_simp; nlinarith [hx c]) (by linarith)]
    field_simp
    ring
  have hmem : priceOf I v.z ∈ priceBox I := priceOf_mem I hI ⟨fun j => (h5 j).1, fun j => (h5 j).2⟩
  have hq : chi x v.δp v.δm = q0 I (priceOf I v.z) := by
    funext c
    rw [hchi, q0_eq, zOf_priceOf I hI hzpos]
  refine ⟨⟨fun c => ?_, fun c => ?_⟩, hq ▸ ⟨_, hmem, rfl⟩⟩
  · -- lower end
    have h4c := h4 c
    have e := h1 c
    have hlo := xLo_pos I x r c
    have hyl : ∑ j, s I c j * v.z j ≤ (1 - xLo I x r c) / xLo I x r c := by
      unfold mu at h4c e; linarith
    rw [le_div_iff₀ hlo] at hyl
    show xLo I x r c ≤ chi x v.δp v.δm c
    rw [hchi, le_div_iff₀ (by linarith [hy c])]
    linarith
  · have h3c := h3 c
    have e := h1 c
    have hhi := xHi_pos I hx hr c
    have hyl : (1 - xHi I x r c) / xHi I x r c ≤ ∑ j, s I c j * v.z j := by
      unfold mu at h3c e; linarith
    rw [div_le_iff₀ hhi] at hyl
    show chi x v.δp v.δm c ≤ xHi I x r c
    rw [hchi, div_le_iff₀ (by linarith [hy c])]
    linarith

lemma zOf_inj (hI : Standing I) : Function.Injective (zOf I) := by
  intro p p' h
  funext j
  have := congrFun h j
  unfold zOf at this
  have := Real.exp_injective this
  have hb := (hI.b_pos j).ne'
  have : (p j - p' j) * I.b j = 0 := by linarith
  rcases mul_eq_zero.mp this with h1 | h1
  · linarith
  · exact absurd h1 hb

lemma q_eq_of (c : Fin m) (j : Fin n) (p : Fin n → ℝ) :
    q I c j p = s I c j * zOf I p j * q0 I p c := by
  unfold q q0
  rw [s_mul_zOf]; ring

lemma obj_eq (hI : Standing I) (x : Fin m → ℝ) (p : Fin n → ℝ) (hq : ∀ c, q0 I p c = x c) :
    Pi I p = cnstrObj I x (zOf I p) := by
  have hlog : ∀ j, Real.log (zOf I p j) = -(p j) * I.b j := fun j => by
    unfold zOf; rw [Real.log_exp]
  have hqq : ∀ c j, q I c j p = s I c j * zOf I p j * x c := fun c j => by
    rw [q_eq_of, hq]
  unfold Pi cnstrObj kx
  simp only [hqq, hlog]
  calc ∑ c, I.w c * ∑ j, p j * (s I c j * zOf I p j * x c)
      = ∑ c, ∑ j, I.w c * (p j * (s I c j * zOf I p j * x c)) := by
        simp_rw [Finset.mul_sum]
    _ = ∑ j, ∑ c, I.w c * (p j * (s I c j * zOf I p j * x c)) := Finset.sum_comm
    _ = -∑ j, zOf I p j * (-p j * I.b j) * ((I.b j)⁻¹ * ∑ c, I.w c * s I c j * x c) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hb := (hI.b_pos j).ne'
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun c _ => ?_
        field_simp

theorem lemma1 (hI : Standing I) (x : Fin m → ℝ) (hx : x ∈ Xset I) :
    Set.BijOn (zOf I) {p | p ∈ priceBox I ∧ ∀ c, q0 I p c = x c} (cnstrFeasible I x) ∧
      (∀ p ∈ priceBox I, (∀ c, q0 I p c = x c) → Pi I p = cnstrObj I x (zOf I p)) ∧
      ConcaveOn ℝ (Set.Icc (zLo I) (zHi I)) (cnstrObj I x) := by
  refine ⟨⟨?_, (zOf_inj I hI).injOn, ?_⟩, fun p _ hq => obj_eq I hI x p hq, ?_⟩
  · rintro p ⟨hp, hq⟩
    refine ⟨zOf_mem I hI hp, fun c => ?_⟩
    rw [← hq c, q0_eq, one_div_one_div]
  · rintro z ⟨hz, hzc⟩
    have hpos : ∀ j, 0 < z j := fun j => (zLo_pos I j).trans_le (hz.1 j)
    refine ⟨priceOf I z, ⟨priceOf_mem I hI hz, fun c => ?_⟩, zOf_priceOf I hI hpos⟩
    rw [q0_eq, zOf_priceOf I hI hpos, hzc c, one_div_one_div]
  · have hxpos : ∀ c, 0 < x c := by
      obtain ⟨p, -, rfl⟩ := hx
      exact fun c => q0_pos I p c
    have hk : ∀ j, 0 ≤ kx I j x := fun j => by
      unfold kx
      exact mul_nonneg (inv_pos.mpr (hI.b_pos j)).le
        (Finset.sum_nonneg fun c _ => by
          have := hI.w_pos c; have := Real.exp_pos (I.a c j); have := hxpos c
          unfold s; positivity)
    have hf : ∀ w : Fin n → ℝ, cnstrObj I x w = ∑ j, kx I j x * Real.negMulLog (w j) := by
      intro w
      unfold cnstrObj Real.negMulLog
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    refine ⟨convex_Icc _ _, ?_⟩
    intro u hu v hv a b ha hb hab
    rw [hf, hf, hf]
    simp only [smul_eq_mul, Pi.add_apply, Pi.smul_apply, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have hu0 : u j ∈ Set.Ici (0 : ℝ) := ((zLo_pos I j).trans_le (hu.1 j)).le
    have hv0 : v j ∈ Set.Ici (0 : ℝ) := ((zLo_pos I j).trans_le (hv.1 j)).le
    have h := Real.concaveOn_negMulLog.2 hu0 hv0 ha hb hab
    simp only [smul_eq_mul] at h
    have := mul_le_mul_of_nonneg_left h (hk j)
    linarith

lemma feas_eq (x : Fin m → ℝ) : cnstrFeasible I x =
    Set.Icc (zLo I) (zHi I) ∩ ⋂ c, {z | 1 + ∑ j, s I c j * z j = 1 / x c} := by
  ext z; simp [cnstrFeasible]

lemma feas_compact (x : Fin m → ℝ) : IsCompact (cnstrFeasible I x) := by
  rw [feas_eq]
  exact isCompact_Icc.inter_right (isClosed_iInter fun c => isClosed_eq (by fun_prop)
    continuous_const)

lemma obj_cont (x : Fin m → ℝ) : Continuous (cnstrObj I x) := by
  unfold cnstrObj
  fun_prop

lemma piX_eq_of_max {x : Fin m → ℝ} {z : Fin n → ℝ} (hz : IsCnstrMax I x z) :
    piX I x = cnstrObj I x z := by
  have : IsGreatest (cnstrObj I x '' cnstrFeasible I x) (cnstrObj I x z) :=
    ⟨Set.mem_image_of_mem _ hz.1, by rintro _ ⟨z', hz', rfl⟩; exact hz.2 z' hz'⟩
  exact this.csSup_eq

lemma le_piX {x : Fin m → ℝ} {z : Fin n → ℝ} (hz : z ∈ cnstrFeasible I x) :
    cnstrObj I x z ≤ piX I x :=
  le_csSup ((feas_compact I x).bddAbove_image (obj_cont I x).continuousOn)
    (Set.mem_image_of_mem _ hz)

lemma q0_priceOf_of_feas (hI : Standing I) {x : Fin m → ℝ} {z : Fin n → ℝ}
    (hz : z ∈ cnstrFeasible I x) : ∀ c, q0 I (priceOf I z) c = x c := by
  intro c
  have hpos : ∀ j, 0 < z j := fun j => (zLo_pos I j).trans_le (hz.1.1 j)
  rw [q0_eq, zOf_priceOf I hI hpos, hz.2 c, one_div_one_div]

lemma Pi_priceOf_of_feas (hI : Standing I) {x : Fin m → ℝ} {z : Fin n → ℝ}
    (hz : z ∈ cnstrFeasible I x) : Pi I (priceOf I z) = cnstrObj I x z := by
  have hpos : ∀ j, 0 < z j := fun j => (zLo_pos I j).trans_le (hz.1.1 j)
  rw [obj_eq I hI x _ (q0_priceOf_of_feas I hI hz), zOf_priceOf I hI hpos]

lemma piX_spec (hI : Standing I) {x : Fin m → ℝ} (hx : x ∈ Xset I) :
    (∃ p ∈ priceBox I, (∀ c, q0 I p c = x c) ∧ piX I x = Pi I p) ∧
      ∀ p ∈ priceBox I, (∀ c, q0 I p c = x c) → Pi I p ≤ piX I x := by
  have hne : (cnstrFeasible I x).Nonempty := by
    obtain ⟨p, hp, rfl⟩ := hx
    exact ⟨zOf I p, zOf_mem I hI hp, fun c => by rw [q0_eq, one_div_one_div]⟩
  obtain ⟨z, hz, hmax⟩ := (feas_compact I x).exists_isMaxOn hne (obj_cont I x).continuousOn
  have hzm : IsCnstrMax I x z := ⟨hz, fun z' hz' => hmax hz'⟩
  refine ⟨⟨priceOf I z, priceOf_mem I hI hz.1, q0_priceOf_of_feas I hI hz, ?_⟩, ?_⟩
  · rw [piX_eq_of_max I hzm, Pi_priceOf_of_feas I hI hz]
  · intro p hp hq
    rw [obj_eq I hI x p hq]
    exact le_piX I ⟨zOf_mem I hI hp, fun c => by rw [← hq c, q0_eq, one_div_one_div]⟩

lemma q_pos (c : Fin m) (i : Fin n) (p : Fin n → ℝ) : 0 < q I c i p := by
  unfold q; exact div_pos (Real.exp_pos _) (denom_pos I c p)

lemma term_le (hI : Standing I) (c : Fin m) (i : Fin n) (p : Fin n → ℝ) :
    p i * q I c i p ≤ Real.exp (I.a c i - 1) / I.b i := by
  have hb := hI.b_pos i
  have hq := q_pos I c i p
  rcases le_or_gt (p i) 0 with hp | hp
  · have : p i * q I c i p ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hp hq.le
    exact this.trans (div_pos (Real.exp_pos _) hb).le
  · have hqle : q I c i p ≤ Real.exp (I.a c i - I.b i * p i) := by
      unfold q
      apply div_le_self (Real.exp_pos _).le
      unfold denom
      have : 0 ≤ ∑ j, Real.exp (I.a c j - I.b j * p j) :=
        Finset.sum_nonneg fun j _ => (Real.exp_pos _).le
      linarith
    have h1 : p i * q I c i p ≤ p i * Real.exp (I.a c i - I.b i * p i) :=
      mul_le_mul_of_nonneg_left hqle hp.le
    have h2 : I.b i * p i ≤ Real.exp (I.b i * p i - 1) := by
      have := Real.add_one_le_exp (I.b i * p i - 1); linarith
    have h3 : Real.exp (I.a c i - I.b i * p i) * Real.exp (I.b i * p i - 1)
        = Real.exp (I.a c i - 1) := by rw [← Real.exp_add]; ring_nf
    rw [le_div_iff₀ hb]
    have he := Real.exp_pos (I.a c i - I.b i * p i)
    calc p i * q I c i p * I.b i ≤ p i * Real.exp (I.a c i - I.b i * p i) * I.b i :=
          mul_le_mul_of_nonneg_right h1 hb.le
      _ = Real.exp (I.a c i - I.b i * p i) * (I.b i * p i) := by ring
      _ ≤ Real.exp (I.a c i - I.b i * p i) * Real.exp (I.b i * p i - 1) :=
          mul_le_mul_of_nonneg_left h2 he.le
      _ = Real.exp (I.a c i - 1) := h3

lemma segRev_bdd (hI : Standing I) (c : Fin m) :
    BddAbove (Set.range fun p : Fin n → ℝ => ∑ i, p i * q I c i p) := by
  refine ⟨∑ i, Real.exp (I.a c i - 1) / I.b i, ?_⟩
  rintro _ ⟨p, rfl⟩
  exact Finset.sum_le_sum fun i _ => term_le I hI c i p

lemma segRev_pLo_pos (hI : Standing I) (c : Fin m) :
    0 < ∑ i, pLo I i * q I c i (pLo I) := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hI.n_pos⟩, Finset.mem_univ _⟩
  exact Finset.sum_pos (fun i _ => mul_pos (inv_pos.mpr (hI.b_pos i)) (q_pos I c i _)) hne

lemma segMax_pos (hI : Standing I) (c : Fin m) : 0 < segMax I c :=
  (segRev_pLo_pos I hI c).trans_le (le_csSup (segRev_bdd I hI c) ⟨pLo I, rfl⟩)

lemma pLo_lt_pHi (hI : Standing I) (j : Fin n) : pLo I j < pHi I j := by
  have hc : 0 < segMax I ⟨0, hI.m_pos⟩ := segMax_pos I hI _
  have : segMax I ⟨0, hI.m_pos⟩ ≤ ⨆ c : Fin m, segMax I c :=
    le_ciSup (Finite.bddAbove_range _) _
  simp only [pLo, pHi]; linarith

lemma pLo_mem (hI : Standing I) : pLo I ∈ priceBox I :=
  ⟨le_rfl, fun j => (pLo_lt_pHi I hI j).le⟩

lemma Pi_cont : Continuous (Pi I) := by
  unfold Pi
  refine continuous_finset_sum _ fun c _ => continuous_const.mul
    (continuous_finset_sum _ fun j _ => (continuous_apply j).mul ?_)
  unfold q
  refine Continuous.div (by fun_prop) ?_ (fun p => (denom_pos I c p).ne')
  unfold denom; fun_prop

/-- Equation (5) in the strong form: a maximizer `p₀` of `Π` on the box gives a maximizer
`q_0(p₀)` of `π` on `X`, with the same value. -/
lemma eq5_core (hI : Standing I) {p₀ : Fin n → ℝ} (hp₀ : p₀ ∈ priceBox I)
    (hmax : ∀ p ∈ priceBox I, Pi I p ≤ Pi I p₀) :
    q0 I p₀ ∈ Xset I ∧ piX I (q0 I p₀) = Pi I p₀ ∧ ∀ x ∈ Xset I, piX I x ≤ Pi I p₀ := by
  have hx₀ : q0 I p₀ ∈ Xset I := ⟨p₀, hp₀, rfl⟩
  have hle : ∀ x ∈ Xset I, piX I x ≤ Pi I p₀ := by
    intro x hx
    obtain ⟨⟨p, hp, -, he⟩, -⟩ := piX_spec I hI hx
    rw [he]; exact hmax p hp
  refine ⟨hx₀, le_antisymm (hle _ hx₀) ((piX_spec I hI hx₀).2 p₀ hp₀ fun c => rfl), hle⟩

lemma exists_box_max (hI : Standing I) :
    ∃ p₀ ∈ priceBox I, ∀ p ∈ priceBox I, Pi I p ≤ Pi I p₀ := by
  obtain ⟨p₀, hp₀, h⟩ := (isCompact_Icc : IsCompact (priceBox I)).exists_isMaxOn
    ⟨pLo I, pLo_mem I hI⟩ (Pi_cont I).continuousOn
  exact ⟨p₀, hp₀, fun p hp => h hp⟩

section Deriv

variable (p : Fin n → ℝ) (j : Fin n)

noncomputable def eC (c : Fin m) (t : ℝ) : ℝ := Real.exp (I.a c j - I.b j * t)
noncomputable def AC (c : Fin m) : ℝ :=
  ∑ i ∈ Finset.univ.erase j, p i * Real.exp (I.a c i - I.b i * p i)
noncomputable def BC (c : Fin m) : ℝ :=
  1 + ∑ i ∈ Finset.univ.erase j, Real.exp (I.a c i - I.b i * p i)
noncomputable def phi (c : Fin m) (t : ℝ) : ℝ :=
  (t * eC I j c t + AC I p j c) / (eC I j c t + BC I p j c)

lemma BC_pos (c : Fin m) : 0 < BC I p j c := by
  unfold BC; positivity

lemma denom_update (c : Fin m) (t : ℝ) :
    denom I c (Function.update p j t) = eC I j c t + BC I p j c := by
  unfold denom eC BC
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), Function.update_self]
  rw [Finset.sum_congr rfl (fun i hi => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)])]
  ring

lemma q_update (c : Fin m) (t : ℝ) :
    q I c j (Function.update p j t) = eC I j c t / (eC I j c t + BC I p j c) := by
  unfold q
  rw [denom_update, Function.update_self]
  rfl

lemma R_update (c : Fin m) (t : ℝ) :
    ∑ i, Function.update p j t i * q I c i (Function.update p j t) = phi I p j c t := by
  unfold phi
  simp only [q, denom_update]
  simp_rw [mul_div_assoc']
  rw [← Finset.sum_div, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  simp only [Function.update_self]
  rw [Finset.sum_congr rfl (fun i hi => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)])]
  unfold eC AC
  ring

lemma Pi_update (t : ℝ) :
    Pi I (Function.update p j t) = ∑ c, I.w c * phi I p j c t := by
  unfold Pi
  simp only [R_update]

lemma hasDerivAt_phi (c : Fin m) (t : ℝ) :
    HasDerivAt (phi I p j c)
      (eC I j c t / (eC I j c t + BC I p j c) * (1 - I.b j * t + I.b j * phi I p j c t)) t := by
  have he : HasDerivAt (eC I j c) (eC I j c t * (-I.b j)) t := by
    unfold eC
    have := (((hasDerivAt_id t).const_mul (I.b j)).const_sub (I.a c j)).exp
    convert this using 1
    · rfl
    · show _ = Real.exp (I.a c j - I.b j * t) * -(I.b j * 1)
      ring
  have hnum : HasDerivAt (fun t => t * eC I j c t + AC I p j c)
      (1 * eC I j c t + t * (eC I j c t * (-I.b j))) t :=
    ((hasDerivAt_id t).mul he).add_const _
  have hden : HasDerivAt (fun t => eC I j c t + BC I p j c) (eC I j c t * (-I.b j)) t :=
    he.add_const _
  have hpos : 0 < eC I j c t + BC I p j c := by
    have := BC_pos I p j c; have : 0 < eC I j c t := Real.exp_pos _; linarith
  have := hnum.div hden hpos.ne'
  have hne := hpos.ne'
  have hval : eC I j c t / (eC I j c t + BC I p j c) * (1 - I.b j * t + I.b j * phi I p j c t)
      = ((1 * eC I j c t + t * (eC I j c t * (-I.b j))) * (eC I j c t + BC I p j c)
        - (t * eC I j c t + AC I p j c) * (eC I j c t * (-I.b j))) /
        (eC I j c t + BC I p j c) ^ 2 := by
    unfold phi; field_simp; ring
  rw [hval]; exact this

lemma hasDerivAt_g (t : ℝ) :
    HasDerivAt (fun t => Pi I (Function.update p j t))
      (∑ c, I.w c * (eC I j c t / (eC I j c t + BC I p j c) *
        (1 - I.b j * t + I.b j * phi I p j c t))) t := by
  have : (fun t => Pi I (Function.update p j t)) = fun t => ∑ c, I.w c * phi I p j c t := by
    funext t; exact Pi_update I p j t
  rw [this]
  exact HasDerivAt.fun_sum fun c _ => (hasDerivAt_phi I p j c t).const_mul _

end Deriv

lemma Sbound (hI : Standing I) (c : Fin m) (p : Fin n → ℝ) :
    ∑ i, p i * q I c i p ≤ ⨆ c : Fin m, segMax I c :=
  le_trans (le_csSup (segRev_bdd I hI c) ⟨p, rfl⟩)
    (le_ciSup (f := fun c => segMax I c) (Finite.bddAbove_range _) c)

lemma Rnonneg (c : Fin m) {p : Fin n → ℝ} (hp : 0 ≤ p) : 0 ≤ ∑ i, p i * q I c i p :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (q_pos I c i p).le

lemma deriv_g_eq (p : Fin n → ℝ) (j : Fin n) :
    deriv (fun t => Pi I (Function.update p j t)) = fun t =>
      ∑ c, I.w c * (q I c j (Function.update p j t) *
        (1 - I.b j * t + I.b j * ∑ i, Function.update p j t i *
          q I c i (Function.update p j t))) := by
  funext t
  rw [(hasDerivAt_g I p j t).deriv]
  simp only [q_update, R_update]

lemma g_cont (p : Fin n → ℝ) (j : Fin n) :
    Continuous (fun t => Pi I (Function.update p j t)) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_g I p j t).continuousAt

lemma clamp_coord (hI : Standing I) (p : Fin n → ℝ) (hp : 0 ≤ p) (j : Fin n) :
    ∃ t ∈ Set.Icc (pLo I j) (pHi I j), Pi I p ≤ Pi I (Function.update p j t) := by
  have hb := hI.b_pos j
  have hupd : ∀ t, 0 ≤ t → 0 ≤ Function.update p j t := fun t ht i => by
    by_cases h : i = j
    · subst h; simp [ht]
    · rw [Function.update_of_ne h]; exact hp i
  have hdiff : Differentiable ℝ (fun t => Pi I (Function.update p j t)) :=
    fun t => (hasDerivAt_g I p j t).differentiableAt
  have hpj : Pi I p = Pi I (Function.update p j (p j)) := by rw [Function.update_eq_self]
  have hpLo : pLo I j = (I.b j)⁻¹ := rfl
  rcases lt_or_ge (p j) (pLo I j) with h1 | h1
  · refine ⟨pLo I j, ⟨le_rfl, (pLo_lt_pHi I hI j).le⟩, ?_⟩
    have hmono : MonotoneOn (fun t => Pi I (Function.update p j t)) (Set.Icc 0 (pLo I j)) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (g_cont I p j).continuousOn
        hdiff.differentiableOn
      intro x hx
      rw [interior_Icc] at hx
      rw [deriv_g_eq]
      refine Finset.sum_nonneg fun c _ => mul_nonneg (hI.w_pos c).le
        (mul_nonneg (q_pos I c j _).le ?_)
      have := Rnonneg I c (hupd x hx.1.le)
      have : I.b j * x ≤ 1 := by
        have := hx.2; rw [hpLo] at this
        calc I.b j * x ≤ I.b j * (I.b j)⁻¹ := by nlinarith
          _ = 1 := mul_inv_cancel₀ hb.ne'
      nlinarith
    rw [hpj]
    exact hmono ⟨hp j, h1.le⟩ ⟨(inv_pos.mpr hb).le, le_rfl⟩ h1.le
  rcases le_or_gt (p j) (pHi I j) with h2 | h2
  · exact ⟨p j, ⟨h1, h2⟩, by rw [Function.update_eq_self]⟩
  · refine ⟨pHi I j, ⟨(pLo_lt_pHi I hI j).le, le_rfl⟩, ?_⟩
    have hanti : AntitoneOn (fun t => Pi I (Function.update p j t)) (Set.Ici (pHi I j)) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ici _) (g_cont I p j).continuousOn
        hdiff.differentiableOn
      intro x hx
      rw [interior_Ici] at hx
      rw [deriv_g_eq]
      refine Finset.sum_nonpos fun c _ => mul_nonpos_of_nonneg_of_nonpos (hI.w_pos c).le
        (mul_nonpos_of_nonneg_of_nonpos (q_pos I c j _).le ?_)
      have hS := Sbound I hI c (Function.update p j x)
      have hx' : (I.b j)⁻¹ + ⨆ c : Fin m, segMax I c < x := hx
      have : I.b j * ((I.b j)⁻¹ + ⨆ c : Fin m, segMax I c) < I.b j * x :=
        mul_lt_mul_of_pos_left hx' hb
      rw [mul_add, mul_inv_cancel₀ hb.ne'] at this
      nlinarith
    rw [hpj]
    exact hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr h2.le) h2.le

lemma clamp_all (hI : Standing I) : ∀ k : ℕ, ∀ p : Fin n → ℝ, 0 ≤ p →
    ∃ p' : Fin n → ℝ, 0 ≤ p' ∧ Pi I p ≤ Pi I p' ∧
      ∀ j : Fin n, j.val < k → p' j ∈ Set.Icc (pLo I j) (pHi I j) := by
  intro k
  induction k with
  | zero => exact fun p hp => ⟨p, hp, le_rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro p hp
    obtain ⟨p', hp'0, hp'le, hp'box⟩ := ih p hp
    by_cases hk : k < n
    · obtain ⟨t, ht, hle⟩ := clamp_coord I hI p' hp'0 ⟨k, hk⟩
      have ht0 : 0 ≤ t := (inv_pos.mpr (hI.b_pos _)).le.trans ht.1
      refine ⟨Function.update p' ⟨k, hk⟩ t, fun i => ?_, hp'le.trans hle, fun i hi => ?_⟩
      · by_cases h : i = ⟨k, hk⟩
        · subst h; simp [ht0]
        · rw [Function.update_of_ne h]; exact hp'0 i
      · by_cases h : i = ⟨k, hk⟩
        · subst h; simp [ht]
        · rw [Function.update_of_ne h]
          apply hp'box
          have : i.val ≠ k := fun h' => h (Fin.ext h')
          omega
    · exact ⟨p', hp'0, hp'le, fun j hj => hp'box j (by omega)⟩

lemma Pi_le_pos (p : Fin n → ℝ) (hI : Standing I) :
    Pi I p ≤ Pi I (fun i => max (p i) 0) := by
  unfold Pi
  refine Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun i _ => ?_) (hI.w_pos c).le
  have hD : denom I c (fun i => max (p i) 0) ≤ denom I c p := by
    unfold denom
    refine (add_le_add_iff_left 1).mpr (Finset.sum_le_sum fun k _ => ?_)
    exact Real.exp_le_exp.mpr (by nlinarith [hI.b_pos k, le_max_left (p k) 0])
  rcases lt_or_ge (p i) 0 with h | h
  · have : max (p i) 0 = 0 := max_eq_right h.le
    simp only [this, zero_mul]
    exact mul_nonpos_of_nonpos_of_nonneg h.le (q_pos I c i p).le
  · have : max (p i) 0 = p i := max_eq_left h
    simp only [this]
    apply mul_le_mul_of_nonneg_left _ h
    unfold q
    simp only [this]
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le (denom_pos I c _) hD

theorem prop1 (hI : Standing I) :
    (∃ pstar : Fin n → ℝ, ∀ p, Pi I p ≤ Pi I pstar) ∧
      ∀ pstar : Fin n → ℝ, (∀ p, Pi I p ≤ Pi I pstar) →
        ∀ j, pLo I j ≤ pstar j ∧ pstar j ≤ pHi I j := by
  constructor
  · obtain ⟨p₀, hp₀, hmax⟩ := exists_box_max I hI
    refine ⟨p₀, fun p => ?_⟩
    obtain ⟨p', -, hle, hbox⟩ := clamp_all I hI n (fun i => max (p i) 0)
      (fun i => le_max_right _ _)
    exact (Pi_le_pos I p hI).trans (hle.trans (hmax p'
      ⟨fun j => (hbox j j.isLt).1, fun j => (hbox j j.isLt).2⟩))
  · intro ps hps
    set R : Fin m → ℝ := fun c => ∑ i, ps i * q I c i ps with hR
    -- first-order conditions
    have hfoc : ∀ j, ∑ c, I.w c * (q I c j ps * (1 - I.b j * ps j + I.b j * R c)) = 0 := by
      intro j
      have hloc : IsLocalMax (fun t => Pi I (Function.update ps j t)) (ps j) :=
        Filter.Eventually.of_forall fun t => by
          simp only [Function.update_eq_self]; exact hps _
      have := hloc.hasDerivAt_eq_zero (hasDerivAt_g I ps j (ps j))
      rw [← this]
      refine Finset.sum_congr rfl fun c _ => ?_
      have hq' : q I c j ps = eC I j c (ps j) / (eC I j c (ps j) + BC I ps j c) := by
        have := q_update I ps j c (ps j); rwa [Function.update_eq_self] at this
      have hR' : R c = phi I ps j c (ps j) := by
        have := R_update I ps j c (ps j); rwa [Function.update_eq_self] at this
      rw [hq', hR']
    have hmne : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, hI.m_pos⟩, Finset.mem_univ _⟩
    obtain ⟨c0, -, hc0⟩ := Finset.exists_min_image Finset.univ R hmne
    obtain ⟨c1, -, hc1⟩ := Finset.exists_max_image Finset.univ R hmne
    -- weighted average bounds
    have hbounds : ∀ j, (I.b j)⁻¹ + R c0 ≤ ps j ∧ ps j ≤ (I.b j)⁻¹ + R c1 := by
      intro j
      have hb := hI.b_pos j
      have hSpos : 0 < ∑ c, I.w c * q I c j ps :=
        Finset.sum_pos (fun c _ => mul_pos (hI.w_pos c) (q_pos I c j ps)) hmne
      have e := hfoc j
      have e2 : (I.b j * ps j - 1) * ∑ c, I.w c * q I c j ps =
          I.b j * ∑ c, I.w c * q I c j ps * R c := by
        rw [Finset.mul_sum, Finset.mul_sum]
        have : ∑ c, I.w c * (q I c j ps * (1 - I.b j * ps j + I.b j * R c)) =
            ∑ c, (I.b j * (I.w c * q I c j ps * R c) - (I.b j * ps j - 1) * (I.w c * q I c j ps)) := by
          refine Finset.sum_congr rfl fun c _ => ?_; ring
        rw [this, Finset.sum_sub_distrib] at e
        linarith
      have hlo : R c0 * ∑ c, I.w c * q I c j ps ≤ ∑ c, I.w c * q I c j ps * R c := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun c _ => by
          have := hc0 c (Finset.mem_univ c)
          have := mul_pos (hI.w_pos c) (q_pos I c j ps)
          nlinarith
      have hhi : ∑ c, I.w c * q I c j ps * R c ≤ R c1 * ∑ c, I.w c * q I c j ps := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun c _ => by
          have := hc1 c (Finset.mem_univ c)
          have := mul_pos (hI.w_pos c) (q_pos I c j ps)
          nlinarith
      have hinv : I.b j * (I.b j)⁻¹ = 1 := mul_inv_cancel₀ hb.ne'
      constructor
      · -- b (ps - 1/b - R c0) S ≥ 0
        have h1 : I.b j * (R c0 * ∑ c, I.w c * q I c j ps) ≤
            (I.b j * ps j - 1) * ∑ c, I.w c * q I c j ps := by
          rw [e2]; exact mul_le_mul_of_nonneg_left hlo hb.le
        have h2 : I.b j * R c0 ≤ I.b j * ps j - 1 := by
          by_contra hcon
          push Not at hcon
          nlinarith
        have h3 : I.b j * ((I.b j)⁻¹ + R c0) ≤ I.b j * ps j := by
          rw [mul_add, hinv]; linarith
        exact le_of_mul_le_mul_left h3 hb
      · have h1 : (I.b j * ps j - 1) * ∑ c, I.w c * q I c j ps ≤
            I.b j * (R c1 * ∑ c, I.w c * q I c j ps) := by
          rw [e2]; exact mul_le_mul_of_nonneg_left hhi hb.le
        have h2 : I.b j * ps j - 1 ≤ I.b j * R c1 := by
          by_contra hcon
          push Not at hcon
          nlinarith
        have h3 : I.b j * ps j ≤ I.b j * ((I.b j)⁻¹ + R c1) := by
          rw [mul_add, hinv]; linarith
        exact le_of_mul_le_mul_left h3 hb
    -- the minimum of R is nonnegative
    have hR0 : 0 ≤ R c0 := by
      by_contra hneg
      push Not at hneg
      have hsumq : ∑ i, q I c0 i ps ≤ 1 := by
        have : ∑ i, q I c0 i ps = (∑ i, Real.exp (I.a c0 i - I.b i * ps i)) / denom I c0 ps := by
          unfold q; rw [Finset.sum_div]
        rw [this, div_le_one (denom_pos I c0 ps)]
        unfold denom; linarith
      have hpos : 0 < ∑ i, (I.b i)⁻¹ * q I c0 i ps := by
        have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hI.n_pos⟩, Finset.mem_univ _⟩
        exact Finset.sum_pos (fun i _ => mul_pos (inv_pos.mpr (hI.b_pos i)) (q_pos I c0 i ps)) hne
      have hge : ∑ i, ((I.b i)⁻¹ * q I c0 i ps + R c0 * q I c0 i ps) ≤ R c0 := by
        show _ ≤ ∑ i, ps i * q I c0 i ps
        exact Finset.sum_le_sum fun i _ => by
          have := (hbounds i).1
          have := q_pos I c0 i ps
          nlinarith
      rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hge
      nlinarith
    intro j
    refine ⟨?_, ?_⟩
    · have := (hbounds j).1
      show (I.b j)⁻¹ ≤ ps j
      linarith
    · have := (hbounds j).2
      have hS := Sbound I hI c1 ps
      show ps j ≤ (I.b j)⁻¹ + ⨆ c : Fin m, segMax I c
      have : R c1 = ∑ i, ps i * q I c1 i ps := rfl
      linarith

end FMLAlg

theorem solution {m n : ℕ} (I : FML m n) (hI : Standing I) :
    (∃ pstar : Fin n → ℝ, ∀ p, Pi I p ≤ Pi I pstar) ∧
      ∀ pstar : Fin n → ℝ, (∀ p, Pi I p ≤ Pi I pstar) →
        ∀ j, pLo I j ≤ pstar j ∧ pstar j ≤ pHi I j :=
  FMLAlg.prop1 I hI
