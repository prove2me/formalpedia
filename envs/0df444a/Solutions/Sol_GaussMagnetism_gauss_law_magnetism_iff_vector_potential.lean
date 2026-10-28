-- Prove2me | solution 1 for GaussMagnetism.gauss_law_magnetism_iff_vector_potential
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:18:30.388242+00:00
-- url     : https://prove2.me/submissions/54dc4a3f-ca70-41a7-8d90-3e0c97f66d3b

import Definitions.Def_GaussMagnetism_box_flux

open Larmor TongEM

namespace GM99

open MeasureTheory

theorem P1 {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (G : E × ℝ → F) (hG : ContDiff ℝ 1 G) (a b : ℝ) (x₀ : E) :
    HasFDerivAt (fun x => ∫ t in a..b, G (x, t))
      (∫ t in a..b, (fderiv ℝ G (x₀, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) x₀ := by
  have hGc : Continuous G := hG.continuous
  have hG'c : Continuous (fun p : E × ℝ => (fderiv ℝ G p).comp (ContinuousLinearMap.inl ℝ E ℝ)) :=
    (hG.continuous_fderiv one_ne_zero).clm_comp continuous_const
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x₀ 1).prod (isCompact_uIcc (a := a) (b := b))).exists_bound_of_continuousOn
    hG'c.continuousOn
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => C)
    (s := Metric.closedBall x₀ 1) (F := fun x t => G (x, t))
    (F' := fun x t => (fderiv ℝ G (x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact Metric.closedBall_mem_nhds _ one_pos
  · exact Filter.Eventually.of_forall (fun x =>
      (hGc.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable)
  · exact (hGc.comp (Continuous.prodMk continuous_const continuous_id)).intervalIntegrable _ _
  · exact (hG'c.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t ht x hx => hC (x, t) ⟨hx, Set.uIoc_subset_uIcc ht⟩)
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall (fun t ht x hx => ?_)
    have h1 : HasFDerivAt G (fderiv ℝ G (x, t)) (x, t) :=
      (hG.differentiable one_ne_zero _).hasFDerivAt
    exact h1.comp x ((hasFDerivAt_id x).prodMk (hasFDerivAt_const t x))

theorem P2 {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] :
    ∀ (n : ℕ) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (G : E × ℝ → F), ContDiff ℝ (⊤ : ℕ∞) G → ∀ a b : ℝ,
      ContDiff ℝ n (fun x => ∫ t in a..b, G (x, t))
  | 0, F, _, _, _, G, hG, a, b => by
    refine contDiff_zero.2 ?_
    exact continuous_iff_continuousAt.2 fun x =>
      (P1 G (hG.of_le (by simp)) a b x).continuousAt
  | n + 1, F, _, _, _, G, hG, a, b => by
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiff_succ_iff_fderiv]
    refine ⟨fun x => (P1 G (hG.of_le (by simp)) a b x).differentiableAt, by simp, ?_⟩
    have hfd : fderiv ℝ (fun x => ∫ t in a..b, G (x, t)) = fun x =>
        ∫ t in a..b, (fun p : E × ℝ => (fderiv ℝ G p).comp (ContinuousLinearMap.inl ℝ E ℝ)) (x, t) := by
      funext x
      exact (P1 G (hG.of_le (by simp)) a b x).fderiv
    rw [hfd]
    exact P2 n (fun p : E × ℝ => (fderiv ℝ G p).comp (ContinuousLinearMap.inl ℝ E ℝ))
      ((hG.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_comp contDiff_const) a b


theorem D (G G' : ℝ → ℝ → ℝ) (hG : Continuous (fun p : ℝ × ℝ => G p.1 p.2))
    (hG' : Continuous (fun p : ℝ × ℝ => G' p.1 p.2))
    (hd : ∀ y s, HasDerivAt (fun y => G y s) (G' y s) y) (α β y₀ : ℝ) :
    HasDerivAt (fun y => ∫ s in α..β, G y s) (∫ s in α..β, G' y₀ s) y₀ := by
  obtain ⟨C, hC⟩ := ((isCompact_closedBall y₀ 1).prod
    (isCompact_uIcc (a := α) (b := β))).exists_bound_of_continuousOn hG'.continuousOn
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => C)
    (s := Metric.closedBall y₀ 1) (F := G) (F' := G') ?_ ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Metric.closedBall_mem_nhds _ one_pos
  · exact Filter.Eventually.of_forall (fun y =>
      (hG.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable)
  · exact (hG.comp (Continuous.prodMk continuous_const continuous_id)).intervalIntegrable _ _
  · exact (hG'.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t ht x hx => hC (x, t) ⟨hx, Set.uIoc_subset_uIcc ht⟩)
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall (fun t _ x _ => hd x t)

theorem Q (g : ℝ → Vec → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec × ℝ => g p.2 p.1))
    (ℓ : Vec → ℝ) (hℓ : ContDiff ℝ (⊤ : ℕ∞) ℓ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ∫ s in (0:ℝ)..ℓ x, g s x) := by
  have h : (fun x => ∫ s in (0:ℝ)..ℓ x, g s x) = fun x => ∫ t in (0:ℝ)..1,
      (fun p : Vec × ℝ => ℓ p.1 * g (ℓ p.1 * p.2) p.1) (x, t) := by
    funext x
    have := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1) (fun s => g s x) (ℓ x)
    simp only [mul_zero, mul_one, smul_eq_mul] at this
    rw [← this, ← intervalIntegral.integral_const_mul]
  rw [h]
  refine contDiff_infty.2 fun n => P2 n (fun p : Vec × ℝ => ℓ p.1 * g (ℓ p.1 * p.2) p.1) ?_ 0 1
  exact (hℓ.comp contDiff_fst).mul
    (hg.comp (contDiff_fst.prodMk ((hℓ.comp contDiff_fst).mul contDiff_snd)))

noncomputable def e (j : Fin 3) : Vec := EuclideanSpace.single j (1:ℝ)
noncomputable def mk (a b c : ℝ) : Vec := a • e 0 + b • e 1 + c • e 2

@[simp] theorem mk0 (a b c : ℝ) : mk a b c 0 = a := by simp [mk, e]
@[simp] theorem mk1 (a b c : ℝ) : mk a b c 1 = b := by simp [mk, e]
@[simp] theorem mk2 (a b c : ℝ) : mk a b c 2 = c := by simp [mk, e]

theorem eta (x : Vec) : mk (x 0) (x 1) (x 2) = x := by
  ext i; fin_cases i <;> simp [mk, e]
theorem line0 (b c t : ℝ) : mk 0 b c + t • e 0 = mk t b c := by
  ext i; fin_cases i <;> simp [mk, e]
theorem line1 (a c t : ℝ) : mk a 0 c + t • e 1 = mk a t c := by
  ext i; fin_cases i <;> simp [mk, e]
theorem line2 (a b t : ℝ) : mk a b 0 + t • e 2 = mk a b t := by
  ext i; fin_cases i <;> simp [mk, e]

theorem mk_contDiff {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞}
    {f g h : X → ℝ} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) (hh : ContDiff ℝ n h) :
    ContDiff ℝ n (fun x => mk (f x) (g x) (h x)) := by
  unfold mk
  exact ((hf.smul contDiff_const).add (hg.smul contDiff_const)).add (hh.smul contDiff_const)

theorem L (F : Vec → Vec) (p v : Vec) (t₀ : ℝ) (i : Fin 3)
    (hF : DifferentiableAt ℝ F (p + t₀ • v)) :
    HasDerivAt (fun t => F (p + t • v) i) (fderiv ℝ F (p + t₀ • v) v i) t₀ := by
  have hc : HasDerivAt (fun t : ℝ => p + t • v) v t₀ := by
    simpa using ((hasDerivAt_id t₀).smul_const v).const_add p
  have h2 := (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t₀
    (hF.hasFDerivAt.comp_hasDerivAt t₀ hc)
  exact h2

theorem U' (F : Vec → Vec) (x v : Vec) (i : Fin 3) (d : ℝ) (hF : DifferentiableAt ℝ F x)
    (h : HasDerivAt (fun t : ℝ => F (x + t • v) i) d 0) : fderiv ℝ F x v i = d := by
  have := L F x v 0 i (by simpa using hF)
  simp only [zero_smul, add_zero] at this
  exact this.unique h

theorem L0 (F : Vec → Vec) (a b c : ℝ) (i : Fin 3) (hF : DifferentiableAt ℝ F (mk a b c)) :
    HasDerivAt (fun t => F (mk t b c) i) (partialDeriv F 0 i (mk a b c)) a := by
  have := L F (mk 0 b c) (e 0) a i (by rwa [line0])
  simp only [line0] at this
  exact this
theorem L1 (F : Vec → Vec) (a b c : ℝ) (i : Fin 3) (hF : DifferentiableAt ℝ F (mk a b c)) :
    HasDerivAt (fun t => F (mk a t c) i) (partialDeriv F 1 i (mk a b c)) b := by
  have := L F (mk a 0 c) (e 1) b i (by rwa [line1])
  simp only [line1] at this
  exact this
theorem L2 (F : Vec → Vec) (a b c : ℝ) (i : Fin 3) (hF : DifferentiableAt ℝ F (mk a b c)) :
    HasDerivAt (fun t => F (mk a b t) i) (partialDeriv F 2 i (mk a b c)) c := by
  have := L F (mk a b 0) (e 2) c i (by rwa [line2])
  simp only [line2] at this
  exact this

theorem cpd (B : Vec → Vec) (hB : ContDiff ℝ 1 B) (j i : Fin 3) :
    Continuous (fun y => partialDeriv B j i y) :=
  (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).continuous.comp
    ((hB.continuous_fderiv one_ne_zero).clm_apply continuous_const)

noncomputable def A1 (B : Vec → Vec) (x : Vec) : ℝ := ∫ s in (0:ℝ)..x 0, B (mk s (x 1) (x 2)) 2
noncomputable def A2 (B : Vec → Vec) (x : Vec) : ℝ :=
  -(∫ s in (0:ℝ)..x 0, B (mk s (x 1) (x 2)) 1) + ∫ s in (0:ℝ)..x 1, B (mk 0 s (x 2)) 0
noncomputable def Apot (B : Vec → Vec) (x : Vec) : Vec := mk 0 (A1 B x) (A2 B x)

theorem hco (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec => y i) :=
  (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).contDiff

theorem mk_cont {X : Type} [TopologicalSpace X] {f g h : X → ℝ} (hf : Continuous f)
    (hg : Continuous g) (hh : Continuous h) : Continuous (fun x => mk (f x) (g x) (h x)) := by
  unfold mk; fun_prop

theorem Apot_smooth (B : Vec → Vec) (hB : SmoothV B) : SmoothV (Apot B) := by
  have hBi : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun y => B y i) := fun i =>
    ContDiff.comp (hco i) hB
  have hA1 : ContDiff ℝ (⊤ : ℕ∞) (A1 B) :=
    Q (fun s x => B (mk s (x 1) (x 2)) 2) ((hBi 2).comp (mk_contDiff contDiff_snd
      ((hco 1).comp contDiff_fst) ((hco 2).comp contDiff_fst))) _ (hco 0)
  have hA2 : ContDiff ℝ (⊤ : ℕ∞) (A2 B) :=
    (Q (fun s x => B (mk s (x 1) (x 2)) 1) ((hBi 1).comp (mk_contDiff contDiff_snd
      ((hco 1).comp contDiff_fst) ((hco 2).comp contDiff_fst))) _ (hco 0)).neg.add
    (Q (fun s x => B (mk 0 s (x 2)) 0) ((hBi 0).comp (mk_contDiff contDiff_const
      contDiff_snd ((hco 2).comp contDiff_fst))) _ (hco 1))
  exact mk_contDiff contDiff_const hA1 hA2

theorem ftc (B : Vec → Vec) (hB : Continuous B) (i : Fin 3) (b c t : ℝ) :
    HasDerivAt (fun t => ∫ s in (0:ℝ)..t, B (mk s b c) i) (B (mk t b c) i) t := by
  have hc : Continuous (fun s => B (mk s b c) i) :=
    (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).continuous.comp
      (hB.comp (mk_cont continuous_id continuous_const continuous_const))
  exact (hc.integral_hasStrictDerivAt 0 t).hasDerivAt

theorem ftc1 (B : Vec → Vec) (hB : Continuous B) (i : Fin 3) (c t : ℝ) :
    HasDerivAt (fun t => ∫ s in (0:ℝ)..t, B (mk 0 s c) i) (B (mk 0 t c) i) t := by
  have hc : Continuous (fun s => B (mk 0 s c) i) :=
    (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).continuous.comp
      (hB.comp (mk_cont continuous_const continuous_id continuous_const))
  exact (hc.integral_hasStrictDerivAt 0 t).hasDerivAt

theorem Apot_curl (B : Vec → Vec) (hB : SmoothV B) (hdiv : ∀ x, divg B x = 0) (a b c : ℝ) :
    curl (Apot B) (mk a b c) = B (mk a b c) := by
  have hB1 : ContDiff ℝ 1 B := hB.of_le (WithTop.coe_le_coe.2 le_top)
  have hBd : Differentiable ℝ B := hB1.differentiable one_ne_zero
  have hcB : ∀ i : Fin 3, Continuous (fun y => B y i) := fun i =>
    (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).continuous.comp hB1.continuous
  have hAd : Differentiable ℝ (Apot B) :=
    ((Apot_smooth B hB).of_le (WithTop.coe_le_coe.2 le_top) : ContDiff ℝ 1 (Apot B)).differentiable
      one_ne_zero
  have p12 : partialDeriv (Apot B) 1 2 (mk a b c) =
      -(∫ s in (0:ℝ)..a, partialDeriv B 1 1 (mk s b c)) + B (mk 0 b c) 0 := by
    refine ((L1 (Apot B) a b c 2 (hAd _)).unique ?_)
    simp only [Apot, A2, mk0, mk1, mk2]
    refine HasDerivAt.add (HasDerivAt.neg ?_) (ftc1 B hB1.continuous 0 c b)
    exact D (fun y s => B (mk s y c) 1) (fun y s => partialDeriv B 1 1 (mk s y c))
      ((hcB 1).comp (mk_cont continuous_snd continuous_fst continuous_const))
      ((cpd B hB1 1 1).comp (mk_cont continuous_snd continuous_fst continuous_const))
      (fun y s => L1 B s y c 1 (hBd _)) 0 a b
  have p21 : partialDeriv (Apot B) 2 1 (mk a b c) =
      ∫ s in (0:ℝ)..a, partialDeriv B 2 2 (mk s b c) := by
    refine ((L2 (Apot B) a b c 1 (hAd _)).unique ?_)
    simp only [Apot, A1, mk0, mk1, mk2]
    exact D (fun y s => B (mk s b y) 2) (fun y s => partialDeriv B 2 2 (mk s b y))
      ((hcB 2).comp (mk_cont continuous_snd continuous_const continuous_fst))
      ((cpd B hB1 2 2).comp (mk_cont continuous_snd continuous_const continuous_fst))
      (fun y s => L2 B s b y 2 (hBd _)) 0 a c
  have p20 : partialDeriv (Apot B) 2 0 (mk a b c) = 0 := by
    refine ((L2 (Apot B) a b c 0 (hAd _)).unique ?_)
    simp only [Apot, mk0]
    exact hasDerivAt_const _ _
  have p10 : partialDeriv (Apot B) 1 0 (mk a b c) = 0 := by
    refine ((L1 (Apot B) a b c 0 (hAd _)).unique ?_)
    simp only [Apot, mk0]
    exact hasDerivAt_const _ _
  have p02 : partialDeriv (Apot B) 0 2 (mk a b c) = -(B (mk a b c) 1) := by
    refine ((L0 (Apot B) a b c 2 (hAd _)).unique ?_)
    simp only [Apot, A2, mk0, mk1, mk2]
    exact ((ftc B hB1.continuous 1 b c a).neg.add_const _)
  have p01 : partialDeriv (Apot B) 0 1 (mk a b c) = B (mk a b c) 2 := by
    refine ((L0 (Apot B) a b c 1 (hAd _)).unique ?_)
    simp only [Apot, A1, mk0, mk1, mk2]
    exact ftc B hB1.continuous 2 b c a
  have hint : ∀ j i : Fin 3,
      IntervalIntegrable (fun s => partialDeriv B j i (mk s b c)) volume 0 a :=
    fun j i => ((cpd B hB1 j i).comp (mk_cont continuous_id continuous_const continuous_const)).intervalIntegrable _ _
  have fund : ∫ s in (0:ℝ)..a, partialDeriv B 0 0 (mk s b c) = B (mk a b c) 0 - B (mk 0 b c) 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => L0 B s b c 0 (hBd _)) (hint 0 0)
  have hd : ∀ s, partialDeriv B 0 0 (mk s b c) =
      -(partialDeriv B 1 1 (mk s b c)) - partialDeriv B 2 2 (mk s b c) := by
    intro s
    have := hdiv (mk s b c)
    simp only [divg, Fin.sum_univ_three] at this
    linarith
  have fund2 : ∫ s in (0:ℝ)..a, partialDeriv B 0 0 (mk s b c) =
      -(∫ s in (0:ℝ)..a, partialDeriv B 1 1 (mk s b c)) -
        ∫ s in (0:ℝ)..a, partialDeriv B 2 2 (mk s b c) := by
    simp_rw [hd]
    rw [intervalIntegral.integral_sub (f := fun s => -partialDeriv B 1 1 (mk s b c)) (hint 1 1).neg (hint 2 2),
      intervalIntegral.integral_neg]
  ext i
  fin_cases i
  · simp [curl, p12, p21]
    linarith
  · simp [curl, p20, p02]
  · simp [curl, p01, p10]

theorem exists_pot (B : Vec → Vec) (hB : SmoothV B) (hdiv : ∀ x, divg B x = 0) :
    ∃ A, SmoothV A ∧ ∀ x, curl A x = B x :=
  ⟨Apot B, Apot_smooth B hB, fun x => by rw [← eta x]; exact Apot_curl B hB hdiv _ _ _⟩
theorem div_curl (A : Vec → Vec) (hA : SmoothV A) (x : Vec) : divg (curl A) x = 0 := by
  have hA2 : ContDiff ℝ 2 A := hA.of_le (WithTop.coe_le_coe.2 le_top)
  have hfd : Differentiable ℝ (fderiv ℝ A) :=
    (hA.fderiv_right (m := 1) (WithTop.coe_le_coe.2 le_top)).differentiable one_ne_zero
  have hsymm := (hA2.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)
  have key : ∀ j k v, HasDerivAt (fun t : ℝ => fderiv ℝ A (x + t • v) (e j) k)
      (fderiv ℝ (fderiv ℝ A) x v (e j) k) 0 := by
    intro j k v
    have := L (fun y => fderiv ℝ A y (e j)) x v 0 k
      (by simpa using (hfd x).clm_apply (differentiableAt_const (e j)))
    simp only [zero_smul, add_zero] at this
    rw [fderiv_clm_apply (hfd x) (differentiableAt_const _)] at this
    simpa using this
  have hpd : ∀ j k, ContDiff ℝ 1 (fun y => partialDeriv A j k y) := fun j k =>
    ContDiff.comp (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).contDiff ((hA.fderiv_right (m := 1) (WithTop.coe_le_coe.2 le_top)).clm_apply contDiff_const)
  have hcd : DifferentiableAt ℝ (curl A) x := by
    have : ContDiff ℝ 1 (curl A) := by
      refine contDiff_piLp' 2 (fun i => ?_)
      fin_cases i
      · exact (hpd 1 2).sub (hpd 2 1)
      · exact (hpd 2 0).sub (hpd 0 2)
      · exact (hpd 0 1).sub (hpd 1 0)
    exact (this.differentiable one_ne_zero) x
  have c0 : partialDeriv (curl A) 0 0 x =
      fderiv ℝ (fderiv ℝ A) x (e 0) (e 1) 2 - fderiv ℝ (fderiv ℝ A) x (e 0) (e 2) 1 :=
    U' (curl A) x (e 0) 0 _ hcd ((key 1 2 (e 0)).sub (key 2 1 (e 0)))
  have c1 : partialDeriv (curl A) 1 1 x =
      fderiv ℝ (fderiv ℝ A) x (e 1) (e 2) 0 - fderiv ℝ (fderiv ℝ A) x (e 1) (e 0) 2 :=
    U' (curl A) x (e 1) 1 _ hcd ((key 2 0 (e 1)).sub (key 0 2 (e 1)))
  have c2 : partialDeriv (curl A) 2 2 x =
      fderiv ℝ (fderiv ℝ A) x (e 2) (e 0) 1 - fderiv ℝ (fderiv ℝ A) x (e 2) (e 1) 0 :=
    U' (curl A) x (e 2) 2 _ hcd ((key 0 1 (e 2)).sub (key 1 0 (e 2)))
  simp only [divg, Fin.sum_univ_three, c0, c1, c2]
  rw [hsymm (e 1) (e 0), hsymm (e 2) (e 0), hsymm (e 2) (e 1)]
  ring

end GM99

open GM99 in
theorem solution (B : Vec → Vec) (hB : SmoothV B) :
    (∀ x, divg B x = 0) ↔ ∃ A : Vec → Vec, SmoothV A ∧ ∀ x, curl A x = B x := by
  constructor
  · exact exists_pot B hB
  · rintro ⟨A, hA, hc⟩ x
    have : curl A = B := funext hc
    rw [← this]
    exact div_curl A hA x
