-- Prove2me | solution 1 for DirKKTBilevel.VP.dir_sum_rule
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T01:04:36.367195+00:00
-- url     : https://prove2.me/submissions/2ee21ac5-1caf-4ecd-9616-df11d76691c8

import Mathlib
import Definitions.Def_DirKKTBilevel_VP_Model

open Filter Topology
open NonconvexSplitting.Shared SetConstrSOC.Directional
open DirKKTBilevel.VP

lemma dk_ereal_shift (X Y : EReal) (r s : ℝ) : (r : EReal) + X ≤ (s : EReal) + Y ↔
    X + ((r - s : ℝ) : EReal) ≤ Y := by
  have e1 : (r : EReal) + X + ((-s : ℝ) : EReal) = X + ((r - s : ℝ) : EReal) := by
    rw [add_comm (r : EReal) X, add_assoc, ← EReal.coe_add, ← sub_eq_add_neg]
  have e2 : (s : EReal) + Y + ((-s : ℝ) : EReal) = Y := by
    rw [add_comm (s : EReal) Y, add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero,
      add_zero]
  have e3 : X + ((r - s : ℝ) : EReal) + (s : EReal) = (r : EReal) + X := by
    rw [add_assoc, ← EReal.coe_add, sub_add_cancel, add_comm]
  have e4 : Y + (s : EReal) = (s : EReal) + Y := add_comm _ _
  constructor
  · intro h
    have := add_le_add_right h ((-s : ℝ) : EReal)
    rwa [add_comm _ ((r : EReal) + X), add_comm _ ((s : EReal) + Y), e1, e2] at this
  · intro h
    have := add_le_add_right h (s : EReal)
    rwa [add_comm _ (X + _), add_comm (s : EReal) Y, e3, e4] at this

lemma dk_regular_sub_smooth {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] (f : X → ℝ) (ψ : X → EReal) (p ζ : X) (hf : DifferentiableAt ℝ f p)
    (h : IsRegularSubgrad (fun z => (f z : EReal) + ψ z) p ζ) :
    IsRegularSubgrad ψ p (ζ - gradient f p) := by
  obtain ⟨hne, hreg⟩ := h
  refine ⟨fun hψ => hne (by show (f p : EReal) + ψ p = ⊤; rw [hψ, EReal.coe_add_top]),
    fun ε hε => ?_⟩
  have hb := hf.hasFDerivAt.isLittleO.def (half_pos hε)
  filter_upwards [hreg (ε / 2) (half_pos hε), hb] with z hz hfz
  rw [Real.norm_eq_abs] at hfz
  have hfz' := (abs_le.mp hfz).2
  have hg : inner ℝ (gradient f p) (z - p) = fderiv ℝ f p (z - p) := by simp [gradient]
  rw [add_comm (f p : EReal) (ψ p), add_assoc, add_comm (ψ p), ← EReal.coe_add,
    dk_ereal_shift] at hz
  refine le_trans (add_le_add_right (EReal.coe_le_coe_iff.mpr ?_) _) hz
  rw [inner_sub_left, hg]
  linarith

lemma dk_regular_add_smooth {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] (f : X → ℝ) (ψ : X → EReal) (p η : X) (hf : DifferentiableAt ℝ f p)
    (h : IsRegularSubgrad ψ p η) :
    IsRegularSubgrad (fun z => (f z : EReal) + ψ z) p (gradient f p + η) := by
  obtain ⟨hne, hreg⟩ := h
  refine ⟨?_, fun ε hε => ?_⟩
  · exact EReal.add_ne_top (EReal.coe_ne_top _) hne
  have hb := hf.hasFDerivAt.isLittleO.def (half_pos hε)
  filter_upwards [hreg (ε / 2) (half_pos hε), hb] with z hz hfz
  show _ ≤ (f z : EReal) + ψ z
  rw [Real.norm_eq_abs] at hfz
  have hfz' := (abs_le.mp hfz).1
  have hg : inner ℝ (gradient f p) (z - p) = fderiv ℝ f p (z - p) := by simp [gradient]
  rw [add_comm (f p : EReal) (ψ p), add_assoc, add_comm (ψ p), ← EReal.coe_add,
    dk_ereal_shift]
  refine le_trans (add_le_add_right (EReal.coe_le_coe_iff.mpr ?_) _) hz
  rw [inner_add_left, hg]
  linarith

/-- Regular subgradients of a function of the first block only. -/
lemma dk_regular_fst {n m : ℕ} (Φ : E n → EReal) (a : E n) (b : E m) (ζ : Z n m)
    (hfin : Φ a ≠ ⊥) (h : IsRegularSubgrad (fun z : Z n m => Φ (WithLp.ofLp z).1)
      (WithLp.toLp 2 (a, b)) ζ) :
    (WithLp.ofLp ζ).2 = 0 ∧ IsRegularSubgrad Φ a (WithLp.ofLp ζ).1 := by
  obtain ⟨hne, hreg⟩ := h
  simp only at hne
  have hcont1 : Continuous (fun a' : E n => (WithLp.toLp 2 (a', b) : Z n m)) := by fun_prop
  refine ⟨?_, hne, fun ε hε => ?_⟩
  · -- second block vanishes
    set β := (WithLp.ofLp ζ).2 with hβ
    by_contra hβ0
    have hβpos : 0 < ‖β‖ := norm_pos_iff.mpr hβ0
    have hcont : Continuous (fun s : ℝ => (WithLp.toLp 2 (a, b + s • β) : Z n m)) := by
      fun_prop
    have hT : Tendsto (fun s : ℝ => (WithLp.toLp 2 (a, b + s • β) : Z n m)) (𝓝[>] 0)
        (𝓝 (WithLp.toLp 2 (a, b))) := by
      have := hcont.tendsto 0
      simp only [zero_smul, add_zero] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    obtain ⟨s, hs, hs0⟩ := ((hT.eventually (hreg (‖β‖ / 2) (half_pos hβpos))).and
      self_mem_nhdsWithin).exists
    have hs0' : (0:ℝ) < s := hs0
    simp only at hs
    have hdiff : (WithLp.toLp 2 (a, b + s • β) : Z n m) - WithLp.toLp 2 (a, b) =
        WithLp.toLp 2 (0, s • β) := by
      rw [← WithLp.toLp_sub, Prod.mk_sub_mk, sub_self, add_sub_cancel_left]
    rw [hdiff] at hs
    have hin : inner ℝ ζ (WithLp.toLp 2 ((0 : E n), s • β) : Z n m) = s * ‖β‖ ^ 2 := by
      rw [WithLp.prod_inner_apply]
      simp only [WithLp.ofLp_toLp, inner_zero_right, zero_add, inner_smul_right]
      rw [show (WithLp.ofLp ζ).2 = β from rfl, real_inner_self_eq_norm_sq]
    have hno : ‖(WithLp.toLp 2 ((0 : E n), s • β) : Z n m)‖ = s * ‖β‖ := by
      rw [WithLp.prod_norm_eq_of_L2]
      simp [norm_smul, abs_of_pos hs0', Real.sqrt_sq (by positivity : 0 ≤ s * ‖β‖)]
    rw [hin, hno] at hs
    -- `Φ a + c ≤ Φ a` with `c > 0` and `Φ a` finite is impossible
    have hc : 0 < s * ‖β‖ ^ 2 - ‖β‖ / 2 * (s * ‖β‖) := by
      have := mul_pos hs0' (pow_pos hβpos 2)
      nlinarith
    induction hΦ : Φ a using EReal.rec with
    | bot => exact hfin hΦ
    | top => exact hne hΦ
    | coe r =>
      rw [hΦ, ← EReal.coe_add, EReal.coe_le_coe_iff] at hs
      linarith
  · have hT : Tendsto (fun a' : E n => (WithLp.toLp 2 (a', b) : Z n m)) (𝓝 a)
        (𝓝 (WithLp.toLp 2 (a, b))) := hcont1.tendsto a
    filter_upwards [hT.eventually (hreg ε hε)] with a' ha'
    have hdiff : (WithLp.toLp 2 (a', b) : Z n m) - WithLp.toLp 2 (a, b) =
        WithLp.toLp 2 (a' - a, 0) := by
      rw [← WithLp.toLp_sub, Prod.mk_sub_mk, sub_self]
    rw [hdiff] at ha'
    have hin : inner ℝ ζ (WithLp.toLp 2 (a' - a, (0 : E m)) : Z n m) =
        inner ℝ (WithLp.ofLp ζ).1 (a' - a) := by
      rw [WithLp.prod_inner_apply]; simp
    have hno : ‖(WithLp.toLp 2 (a' - a, (0 : E m)) : Z n m)‖ = ‖a' - a‖ := by
      rw [WithLp.prod_norm_eq_of_L2]
      simp [Real.sqrt_sq (norm_nonneg _)]
    rwa [hin, hno] at ha'

lemma dk_regular_fst_mk {n m : ℕ} (Φ : E n → EReal) (a : E n) (b : E m) (η : E n)
    (h : IsRegularSubgrad Φ a η) :
    IsRegularSubgrad (fun z : Z n m => Φ (WithLp.ofLp z).1) (WithLp.toLp 2 (a, b))
      (WithLp.toLp 2 (η, 0)) := by
  obtain ⟨hne, hreg⟩ := h
  refine ⟨hne, fun ε hε => ?_⟩
  have hcont : Continuous (fun z : Z n m => (WithLp.ofLp z).1) := by fun_prop
  have hT : Tendsto (fun z : Z n m => (WithLp.ofLp z).1) (𝓝 (WithLp.toLp 2 (a, b))) (𝓝 a) := by
    simpa using hcont.tendsto (WithLp.toLp 2 (a, b))
  filter_upwards [hT.eventually (hreg ε hε)] with z hz
  refine le_trans (add_le_add_right (EReal.coe_le_coe_iff.mpr ?_) _) hz
  have hin : inner ℝ (WithLp.toLp 2 (η, (0 : E m)) : Z n m) (z - WithLp.toLp 2 (a, b)) =
      inner ℝ η ((WithLp.ofLp z).1 - a) := by
    rw [WithLp.prod_inner_apply]; simp
  have hno : ‖(WithLp.ofLp z).1 - a‖ ≤ ‖z - WithLp.toLp 2 (a, b)‖ := by
    rw [WithLp.prod_norm_eq_of_L2]
    apply Real.le_sqrt_of_sq_le
    have : (z - WithLp.toLp 2 (a, b)).fst = (WithLp.ofLp z).1 - a := rfl
    rw [this]
    nlinarith [sq_nonneg ‖(z - WithLp.toLp 2 (a, b)).snd‖]
  rw [hin]
  nlinarith

theorem solution {n m p : ℕ} (f : Z n m → ℝ) (g : Z n m → E p) (hf : ContDiff ℝ 1 f)
    (x : E n) (y : E m) (u : E n) (v : E m)
    (hVbot : valueFn f g x ≠ ⊥) (hVtop : valueFn f g x ≠ ⊤) :
    dirSubdiff (fun z : Z n m => (f z : EReal) - valueFn f g (WithLp.ofLp z).1)
        (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, v)) =
      {w | ∃ ξ ∈ dirSubdiff (fun x' => -(valueFn f g x')) x u,
        w = gradient f (WithLp.toLp 2 (x, y)) + WithLp.toLp 2 (ξ, 0)} := by
  set V := valueFn f g with hV
  set Φ : E n → EReal := fun x' => -(V x') with hΦ
  have hsplit : (fun z : Z n m => (f z : EReal) - V (WithLp.ofLp z).1) =
      fun z => (f z : EReal) + Φ (WithLp.ofLp z).1 := by
    funext z; rw [sub_eq_add_neg]
  have hdf : ∀ z, DifferentiableAt ℝ f z := fun z => hf.differentiable (by norm_num) z
  have hgradc : Continuous (gradient f) := by
    have h1 : Continuous (fun z => fderiv ℝ f z) := hf.continuous_fderiv (by norm_num)
    exact (InnerProductSpace.toDual ℝ (Z n m)).symm.continuous.comp h1
  have hfc : Continuous f := hf.continuous
  set z0 : Z n m := WithLp.toLp 2 (x, y) with hz0
  have hΦx : Φ x = ((-(V x).toReal : ℝ) : EReal) := by
    rw [hΦ]; simp only
    rw [EReal.coe_neg, EReal.coe_toReal hVtop hVbot]
  rw [hsplit]
  ext w
  constructor
  · rintro ⟨hne1, hne2, t, ws, ζs, ht, ht0, hws, hζs, hval, hreg⟩
    -- the values are eventually finite
    have hval0 : (f z0 : EReal) + Φ (WithLp.ofLp z0).1 = ((f z0 - (V x).toReal : ℝ) : EReal) := by
      simp only [hz0, WithLp.ofLp_toLp]
      rw [hΦx, ← EReal.coe_add, sub_eq_add_neg]
    have hevbot : ∀ᶠ k in atTop,
        (f (z0 + t k • ws k) : EReal) + Φ (WithLp.ofLp (z0 + t k • ws k)).1 ≠ ⊥ :=
      hval.eventually (isOpen_ne.mem_nhds (by
        show (f z0 : EReal) + Φ (WithLp.ofLp z0).1 ≠ ⊥
        rw [hval0]; exact EReal.coe_ne_bot _))
    obtain ⟨N, hN⟩ := eventually_atTop.mp hevbot
    -- shift the sequences
    set pk : ℕ → Z n m := fun k => z0 + t (k + N) • ws (k + N) with hpk
    have hpk1 : ∀ k, (WithLp.ofLp (pk k)).1 = x + t (k + N) • (WithLp.ofLp (ws (k + N))).1 := by
      intro k; simp [hpk, hz0]
    have hpk2 : ∀ k, (WithLp.ofLp (pk k)).2 = y + t (k + N) • (WithLp.ofLp (ws (k + N))).2 := by
      intro k; simp [hpk, hz0]
    have hsub : ∀ k, IsRegularSubgrad (fun z : Z n m => Φ (WithLp.ofLp z).1) (pk k)
        (ζs (k + N) - gradient f (pk k)) :=
      fun k => dk_regular_sub_smooth f _ (pk k) (ζs (k + N)) (hdf _) (hreg (k + N))
    have hΦbot : ∀ k, Φ (WithLp.ofLp (pk k)).1 ≠ ⊥ := by
      intro k hb
      have := hN (k + N) (Nat.le_add_left N k)
      apply this
      show (f (pk k) : EReal) + Φ (WithLp.ofLp (pk k)).1 = ⊥
      rw [hb]; simp
    have hproj : ∀ k, (WithLp.ofLp (ζs (k + N) - gradient f (pk k))).2 = 0 ∧
        IsRegularSubgrad Φ (x + t (k + N) • (WithLp.ofLp (ws (k + N))).1)
          (WithLp.ofLp (ζs (k + N) - gradient f (pk k))).1 := by
      intro k
      have h1 := hsub k
      have hpk_eq : pk k = WithLp.toLp 2 ((WithLp.ofLp (pk k)).1, (WithLp.ofLp (pk k)).2) := rfl
      rw [hpk_eq] at h1
      have := dk_regular_fst Φ _ _ _ (hΦbot k) h1
      rw [hpk1 k] at this
      exact this
    have hN' : Tendsto (fun k : ℕ => k + N) atTop atTop := tendsto_add_atTop_nat N
    have htN := ht0.comp hN'
    have hwsN := hws.comp hN'
    have hζN := hζs.comp hN'
    have hpkT : Tendsto pk atTop (𝓝 z0) := by
      have := (tendsto_const_nhds (x := z0)).add (htN.smul hwsN)
      simpa [zero_smul, add_zero] using this
    have hdiffT : Tendsto (fun k => ζs (k + N) - gradient f (pk k)) atTop
        (𝓝 (w - gradient f z0)) :=
      hζN.sub ((hgradc.tendsto z0).comp hpkT)
    have hfst : Continuous (fun z : Z n m => (WithLp.ofLp z).1) := by fun_prop
    have hsnd : Continuous (fun z : Z n m => (WithLp.ofLp z).2) := by fun_prop
    have h2lim : (WithLp.ofLp (w - gradient f z0)).2 = 0 := by
      have := (hsnd.tendsto _).comp hdiffT
      exact tendsto_nhds_unique this (tendsto_const_nhds.congr fun k => ((hproj k).1).symm)
    refine ⟨(WithLp.ofLp (w - gradient f z0)).1, ?_, ?_⟩
    · refine ⟨?_, ?_, fun k => t (k + N), fun k => (WithLp.ofLp (ws (k + N))).1,
        fun k => (WithLp.ofLp (ζs (k + N) - gradient f (pk k))).1, fun k => ht (k + N),
        htN, ?_, (hfst.tendsto _).comp hdiffT, ?_, fun k => (hproj k).2⟩
      · rw [hΦx]; exact EReal.coe_ne_top _
      · rw [hΦx]; exact EReal.coe_ne_bot _
      · have := (hfst.tendsto _).comp hwsN
        rw [WithLp.ofLp_toLp] at this
        exact this
      · -- values of `Φ` converge
        have hvalN : Tendsto (fun k => (f (pk k) : EReal) + Φ (WithLp.ofLp (pk k)).1) atTop
            (𝓝 ((f z0 - (V x).toReal : ℝ) : EReal)) := by
          rw [← hval0]; exact hval.comp hN'
        have hreal : Tendsto (fun k => ((f (pk k) : EReal) + Φ (WithLp.ofLp (pk k)).1).toReal)
            atTop (𝓝 (f z0 - (V x).toReal)) :=
          (EReal.tendsto_toReal (EReal.coe_ne_top _) (EReal.coe_ne_bot _)).comp hvalN
        have hfT : Tendsto (fun k => f (pk k)) atTop (𝓝 (f z0)) := (hfc.tendsto z0).comp hpkT
        have hΦreal := hreal.sub hfT
        have hlim := (continuous_coe_real_ereal.tendsto _).comp hΦreal
        rw [hΦx]
        convert hlim using 1
        · funext k
          simp only [Function.comp_apply]
          rw [← hpk1 k]
          have hΦtop : Φ (WithLp.ofLp (pk k)).1 ≠ ⊤ := (hproj k).2.1 |> fun h => by
            rw [hpk1 k]; exact h
          induction hφ : Φ (WithLp.ofLp (pk k)).1 using EReal.rec with
          | bot => exact absurd hφ (hΦbot k)
          | top => exact absurd hφ hΦtop
          | coe r =>
            rw [← EReal.coe_add, EReal.toReal_coe]
            congr 1; ring
        · congr 1; ring
    · have hdec : w - gradient f z0 =
          WithLp.toLp 2 ((WithLp.ofLp (w - gradient f z0)).1, (0 : E m)) := by
        conv_rhs => rw [← h2lim]
      rw [← hdec]; abel
  · rintro ⟨ξ, ⟨hne1, hne2, t, us, ξs, ht, ht0, hus, hξs, hval, hreg⟩, rfl⟩
    have hVfin : V x ≠ ⊥ ∧ V x ≠ ⊤ := ⟨hVbot, hVtop⟩
    refine ⟨?_, ?_, t, fun k => WithLp.toLp 2 (us k, v), fun k =>
      gradient f (z0 + t k • WithLp.toLp 2 (us k, v)) + WithLp.toLp 2 (ξs k, 0), ht, ht0,
      ?_, ?_, ?_, fun k => ?_⟩
    · simp only [hz0, WithLp.ofLp_toLp]; rw [hΦx, ← EReal.coe_add]; exact EReal.coe_ne_top _
    · simp only [hz0, WithLp.ofLp_toLp]; rw [hΦx, ← EReal.coe_add]; exact EReal.coe_ne_bot _
    · have hc : Continuous (fun a : E n => (WithLp.toLp 2 (a, v) : Z n m)) := by fun_prop
      exact (hc.tendsto u).comp hus
    · have hc : Continuous (fun a : E n => (WithLp.toLp 2 (a, v) : Z n m)) := by fun_prop
      have hpT : Tendsto (fun k => z0 + t k • WithLp.toLp 2 (us k, v)) atTop (𝓝 z0) := by
        have := (tendsto_const_nhds (x := z0)).add (ht0.smul ((hc.tendsto u).comp hus))
        simpa using this
      have h1 := (hgradc.tendsto z0).comp hpT
      have hc2 : Continuous (fun a : E n => (WithLp.toLp 2 (a, (0 : E m)) : Z n m)) := by fun_prop
      exact h1.add ((hc2.tendsto ξ).comp hξs)
    · have hc : Continuous (fun a : E n => (WithLp.toLp 2 (a, v) : Z n m)) := by fun_prop
      have hpT : Tendsto (fun k => z0 + t k • WithLp.toLp 2 (us k, v)) atTop (𝓝 z0) := by
        have := (tendsto_const_nhds (x := z0)).add (ht0.smul ((hc.tendsto u).comp hus))
        simpa using this
      have hfT := (continuous_coe_real_ereal.tendsto _).comp ((hfc.tendsto z0).comp hpT)
      have hfst : ∀ k, (WithLp.ofLp (z0 + t k • WithLp.toLp 2 (us k, v))).1 = x + t k • us k := by
        intro k; simp [hz0]
      have hsum := (EReal.continuousAt_add (p := ((f z0 : EReal), Φ x))
        (Or.inl (EReal.coe_ne_top _)) (Or.inl (EReal.coe_ne_bot _))).tendsto.comp
        (hfT.prodMk_nhds hval)
      simp only [hz0, WithLp.ofLp_toLp]
      convert hsum using 1
      funext k
      simp only [Function.comp_apply]
      rw [hfst k]
    · have h1 := dk_regular_fst_mk Φ (x + t k • us k) (y + t k • v) (ξs k) (hreg k)
      have heq : z0 + t k • WithLp.toLp 2 (us k, v) =
          WithLp.toLp 2 (x + t k • us k, y + t k • v) := by
        rw [hz0, ← WithLp.toLp_smul, ← WithLp.toLp_add]; rfl
      rw [heq]
      exact dk_regular_add_smooth f _ _ _ (hdf _) h1
