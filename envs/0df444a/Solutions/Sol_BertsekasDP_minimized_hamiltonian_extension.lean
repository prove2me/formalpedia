-- Prove2me | solution 1 for BertsekasDP.minimized_hamiltonian_extension
-- status  : ACCEPTED   (prove)
-- author  : @davidnet
-- created : 2026-09-07T21:45:04.654161+00:00
-- url     : https://prove2.me/submissions/e0417b21-2bab-4ece-9328-4bc3d616b4fe

import Definitions.Def_BertsekasCTModel

open Set Filter Asymptotics
open scoped Topology RealInnerProductSpace

/-- The envelope squeeze only needs a continuous minimizing selector. -/
private lemma envelope_zero
    {X V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (H : X × V → ℝ) (hH : ContDiff ℝ 1 H)
    (z : ℝ → X) (v : ℝ → V) (t : ℝ) (z' : X)
    (hz : HasDerivAt z z' t) (hv : ContinuousAt v t)
    (hfixed : HasDerivAt (fun s => H (z s, v t)) 0 t)
    (hmin₁ : ∀ᶠ s in 𝓝 t, H (z s, v s) ≤ H (z s, v t))
    (hmin₂ : ∀ᶠ s in 𝓝 t, H (z t, v t) ≤ H (z t, v s)) :
    HasDerivAt (fun s => H (z s, v s)) 0 t := by
  let D := fderiv ℝ H (z t, v t)
  have hstrict : HasStrictFDerivAt H D (z t, v t) :=
    hH.hasStrictFDerivAt one_ne_zero
  have hbig : (fun s => (z s - z t, (0 : V))) =O[𝓝 t] (fun s => s - t) :=
    hz.isBigO_sub.prod_left (isBigO_zero _ _)
  -- Strict differentiability compares two nearby states at the same moving control.
  have hrem (w : ℝ → V) (hw : Tendsto w (𝓝 t) (𝓝 (v t))) :
      (fun s => H (z s, w s) - H (z t, w s) - D (z s - z t, 0))
        =o[𝓝 t] (fun s => s - t) := by
    have ht : Tendsto (fun s => ((z s, w s), (z t, w s))) (𝓝 t)
        (𝓝 ((z t, v t), (z t, v t))) :=
      (hz.continuousAt.tendsto.prodMk_nhds hw).prodMk_nhds
      (tendsto_const_nhds.prodMk_nhds hw)
    have hr := hstrict.isLittleO.comp_tendsto ht
    have hr' : (fun s => H (z s, w s) - H (z t, w s) - D (z s - z t, 0))
        =o[𝓝 t] (fun s => (z s - z t, (0 : V))) := by
      simpa only [Function.comp_def, Prod.mk_sub_mk, sub_self] using hr
    exact hr'.trans_isBigO hbig
  have hupper : (fun s => H (z s, v t) - H (z t, v t))
      =o[𝓝 t] (fun s => s - t) := by
    simpa using hfixed.isLittleO
  have hlower : (fun s => H (z s, v s) - H (z t, v s))
      =o[𝓝 t] (fun s => s - t) := by
    have hh := ((hrem v hv.tendsto).sub (hrem (fun _ => v t) tendsto_const_nhds)).add
      hupper
    convert hh using 1 <;> first | rfl | (ext s; ring)
  apply HasDerivAt.of_isLittleO
  simp only [smul_zero, sub_zero]
  apply IsLittleO.of_bound
  intro c hc
  filter_upwards [hlower.bound hc, hupper.bound hc, hmin₁, hmin₂]
    with s hl hu hm₁ hm₂
  rw [Real.norm_eq_abs, abs_le] at hl hu ⊢
  constructor <;> linarith

set_option backward.isDefEq.respectTransparency false in
private lemma frozen_hamiltonian_zero
    {n m : ℕ} (M : BertsekasCTModel n m)
    (hf : ContDiff ℝ 1 (Function.uncurry M.f))
    (hg : ContDiff ℝ 1 (Function.uncurry M.g))
    (x p : ℝ → EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin m)) (t : ℝ)
    (hx : HasDerivAt x (M.f (x t) v) t)
    (hp : HasDerivAt p
      (-gradient (fun y => BertsekasHamiltonian M y v (p t)) (x t)) t) :
    HasDerivAt (fun s => BertsekasHamiltonian M (x s) v (p s)) 0 t := by
  have hf₁ : ContDiff ℝ 1 (fun y => M.f y v) :=
    hf.comp (contDiff_id.prodMk contDiff_const)
  have hg₁ : ContDiff ℝ 1 (fun y => M.g y v) :=
    hg.comp (contDiff_id.prodMk contDiff_const)
  have hH : ContDiff ℝ 1 (fun y => BertsekasHamiltonian M y v (p t)) :=
    hg₁.add (contDiff_const.inner ℝ hf₁)
  have h₁ := ((hH.differentiable one_ne_zero (x t)).hasGradientAt.hasFDerivAt).comp_hasDerivAt t hx
  have h₂ := (hp.sub_const (p t)).inner ℝ
    ((hf₁.differentiable one_ne_zero (x t)).hasFDerivAt.comp_hasDerivAt t hx)
  convert h₁.add h₂ using 1 <;> first
  | rfl
  | (funext s; dsimp [BertsekasHamiltonian]; rw [inner_sub_left]; ring)
  | simp

set_option backward.isDefEq.respectTransparency false in
theorem solution
    {n m : ℕ} (M : BertsekasCTModel n m)
    (hf : ContDiff ℝ 1 (Function.uncurry M.f))
    (hg : ContDiff ℝ 1 (Function.uncurry M.g))
    (u : ℝ → EuclideanSpace ℝ (Fin m))
    (x p : ℝ → EuclideanSpace ℝ (Fin n))
    (F : Finset ℝ)
    (huU : ∀ t ∈ Set.Icc 0 M.T, u t ∈ M.U)
    (hub : Bornology.IsBounded (u '' Set.Icc 0 M.T))
    (hu : ContinuousOn u (Set.Icc 0 M.T \ (F : Set ℝ)))
    (hx : ContinuousOn x (Set.Icc 0 M.T))
    (hp : ContinuousOn p (Set.Icc 0 M.T))
    (hstate : ∀ t ∈ Set.Icc 0 M.T \ (F : Set ℝ),
      HasDerivAt x (M.f (x t) (u t)) t)
    (hadj : ∀ t ∈ Set.Icc 0 M.T \ (F : Set ℝ),
      HasDerivAt p
        (-gradient (fun y => BertsekasHamiltonian M y (u t) (p t)) (x t)) t)
    (hmin : ∀ t ∈ Set.Icc 0 M.T \ (F : Set ℝ),
      IsMinOn (fun v => BertsekasHamiltonian M (x t) v (p t)) M.U (u t)) :
    ∃ E : ℝ → ℝ,
      ContinuousOn E (Set.Icc 0 M.T) ∧
      (∀ t ∈ Set.Icc 0 M.T \ (F : Set ℝ),
        E t = BertsekasHamiltonian M (x t) (u t) (p t)) ∧
      (∀ t ∈ Set.Ioo 0 M.T \ (F : Set ℝ), HasDerivAt E 0 t) := by
  let H : ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ×
      EuclideanSpace ℝ (Fin m)) → ℝ :=
    fun z => BertsekasHamiltonian M z.1.1 z.2 z.1.2
  have hH : ContDiff ℝ 1 H :=
    (hg.comp (contDiff_fst.fst.prodMk contDiff_snd)).add
      (contDiff_fst.snd.inner ℝ (hf.comp (contDiff_fst.fst.prodMk contDiff_snd)))
  let K := closure (u '' Icc 0 M.T)
  have hK : IsCompact K := hub.isCompact_closure
  -- Minimize over the closure of the actual control image, which is compact.
  let E : ℝ → ℝ := fun t => sInf ((fun v => H ((x t, p t), v)) '' K)
  have hvalue : Continuous (fun z => sInf ((fun v => H (z, v)) '' K)) :=
    hK.continuous_sInf hH.continuous
  have hE : ContinuousOn E (Icc 0 M.T) :=
    hvalue.comp_continuousOn (hx.prodMk hp)
  have hEeq (t : ℝ) (ht : t ∈ Icc 0 M.T \ (F : Set ℝ)) :
      E t = BertsekasHamiltonian M (x t) (u t) (p t) := by
    have hc : Continuous (fun v => H ((x t, p t), v)) :=
      hH.continuous.comp (continuous_const.prodMk continuous_id)
    have hle : K ⊆ {v | H ((x t, p t), u t) ≤ H ((x t, p t), v)} := by
      -- The minimum inequality extends from the image to its closure.
      apply closure_minimal _ (isClosed_le continuous_const hc)
      rintro v ⟨s, hs, rfl⟩
      exact hmin t ht (huU s hs)
    apply IsLeast.csInf_eq
    refine ⟨mem_image_of_mem _ (subset_closure (mem_image_of_mem u ht.1)), ?_⟩
    rintro y ⟨v, hv, rfl⟩
    exact hle hv
  refine ⟨E, hE, hEeq, ?_⟩
  intro t ht
  have htgood : t ∈ Icc 0 M.T \ (F : Set ℝ) :=
    ⟨⟨ht.1.1.le, ht.1.2.le⟩, ht.2⟩
  have hreg : Icc 0 M.T \ (F : Set ℝ) ∈ 𝓝 t :=
    inter_mem (Icc_mem_nhds ht.1.1 ht.1.2)
      (F.finite_toSet.isClosed.isOpen_compl.mem_nhds ht.2)
  have hfixed : HasDerivAt (fun s => H ((x s, p s), u t)) 0 t :=
    frozen_hamiltonian_zero M hf hg x p (u t) t (hstate t htgood) (hadj t htgood)
  have henv := envelope_zero H hH (fun s => (x s, p s)) u t _
    ((hstate t htgood).prodMk (hadj t htgood)) (hu.continuousAt hreg) hfixed
    (by filter_upwards [hreg] with s hs using hmin s hs (huU t htgood.1))
    (by filter_upwards [hreg] with s hs using hmin t htgood (huU s hs.1))
  exact henv.congr_of_eventuallyEq
    (by filter_upwards [hreg] with s hs using hEeq s hs)
