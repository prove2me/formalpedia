-- Prove2me | solution 1 for EthierKurtz.oblique_hy_semigroup
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-25T05:42:52.606806+00:00
-- url     : https://prove2.me/submissions/feba5823-3ba9-4b01-898b-efd9582c2654

import Mathlib
import Definitions.Def_EthierKurtz_BoundaryCTwiceHolder
import Definitions.Def_EthierKurtz_BoundaryCOnceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_obliqueDiffusionGraph
import Definitions.Def_EthierKurtz_IsStronglyContinuousContractionSemigroup
import Theorems.Thm_EthierKurtz_hille_yosida_closed_dissipative_relation
import Theorems.Thm_EthierKurtz_componentHolder_extends_closure
import Theorems.Thm_EthierKurtz_oblique_flat_lift
import Theorems.Thm_EthierKurtz_oblique_local_corrector

set_option autoImplicit false

open Filter
open scoped Topology BoundedContinuousFunction Manifold ContDiff

namespace Pd67abb68C2

/-- Restrictions of `C^∞` functions, as a subalgebra of `C(K, ℝ)`. -/
def smoothSub {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) : Subalgebra ℝ C(K, ℝ) where
  carrier := {f | ∃ F : EuclideanSpace ℝ (Fin d) → ℝ,
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F ∧ ∀ x : K, f x = F x}
  mul_mem' := by
    rintro f g ⟨F, hF, hf⟩ ⟨G, hG, hg⟩
    exact ⟨fun x => F x * G x, hF.mul hG, fun x => by simp [hf, hg]⟩
  add_mem' := by
    rintro f g ⟨F, hF, hf⟩ ⟨G, hG, hg⟩
    exact ⟨fun x => F x + G x, hF.add hG, fun x => by simp [hf, hg]⟩
  algebraMap_mem' := by
    intro r
    exact ⟨fun _ => r, contDiff_const, fun x => by simp⟩

/-- C2c: smooth functions are uniformly dense on a compact set (Stone-Weierstrass). -/
lemma smooth_approx {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K)
    (φ : K →ᵇ ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ F : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F ∧
      ∀ x : K, |F x - φ x| < δ := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hsep : (smoothSub K).SeparatesPoints := by
    intro x y hxy
    have hne : (x : EuclideanSpace ℝ (Fin d)) ≠ y := fun h => hxy (Subtype.ext h)
    obtain ⟨i, hi⟩ : ∃ i, (x : EuclideanSpace ℝ (Fin d)) i ≠ (y : EuclideanSpace ℝ (Fin d)) i := by
      by_contra h
      push_neg at h
      exact hne (by ext i; exact h i)
    let P : C(K, ℝ) := ⟨fun z => (z : EuclideanSpace ℝ (Fin d)) i, by fun_prop⟩
    have hP : P ∈ smoothSub K :=
      ⟨fun v => v i, (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).contDiff,
        fun z => rfl⟩
    exact ⟨⇑P, ⟨P, hP, rfl⟩, hi⟩
  obtain ⟨g, hg⟩ := ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints
    (smoothSub K) hsep φ φ.continuous δ hδ
  obtain ⟨F, hF, hgF⟩ := g.2
  refine ⟨F, hF, fun x => ?_⟩
  rw [← hgF x]
  simpa [Real.norm_eq_abs] using hg x

end Pd67abb68C2


namespace Pd67abb68

open EthierKurtz

variable {d : ℕ}


lemma restr_lin {Ω : Set (EuclideanSpace ℝ (Fin d))} (c₁ c₂ : ℝ) (f₁ f₂ : (closure Ω) →ᵇ ℝ) :
    closedRegionRestriction (c₁ • f₁ + c₂ • f₂) =
      fun y => c₁ * closedRegionRestriction f₁ y + c₂ * closedRegionRestriction f₂ y := by
  funext y
  unfold closedRegionRestriction
  split_ifs <;> simp

lemma restr_zero {Ω : Set (EuclideanSpace ℝ (Fin d))} :
    closedRegionRestriction (0 : (closure Ω) →ᵇ ℝ) = fun _ => 0 := by
  funext y
  unfold closedRegionRestriction
  split_ifs <;> simp

lemma compHolder_congr {Ω : Set (EuclideanSpace ℝ (Fin d))} {μ : ℝ} {F G : (EuclideanSpace ℝ (Fin d)) → ℝ} (hF : ComponentHolder Ω μ F)
    (h : ∀ x ∈ Ω, G x = F x) : ComponentHolder Ω μ G := by
  obtain ⟨hc, ρ₀, M, hρ, hM, hb⟩ := hF
  refine ⟨hc.congr h, ρ₀, M, hρ, hM, fun ρ h0 h1 x z hz y hy w hw => ?_⟩
  have hyΩ : y ∈ Ω := (connectedComponentIn_subset _ _ hy).1
  have hwΩ : w ∈ Ω := (connectedComponentIn_subset _ _ hw).1
  rw [h y hyΩ, h w hwΩ]
  exact hb ρ h0 h1 x z hz y hy w hw

lemma compHolder_lin {Ω : Set (EuclideanSpace ℝ (Fin d))} {μ : ℝ} (hμ : 0 < μ) {F G : (EuclideanSpace ℝ (Fin d)) → ℝ}
    (hF : ComponentHolder Ω μ F) (hG : ComponentHolder Ω μ G) (c₁ c₂ : ℝ) :
    ComponentHolder Ω μ (fun x => c₁ * F x + c₂ * G x) := by
  obtain ⟨hcF, ρ₁, M₁, hρ₁, hM₁, hb₁⟩ := hF
  obtain ⟨hcG, ρ₂, M₂, hρ₂, hM₂, hb₂⟩ := hG
  refine ⟨(continuousOn_const.mul hcF).add (continuousOn_const.mul hcG), min ρ₁ ρ₂,
    |c₁| * M₁ + |c₂| * M₂, lt_min hρ₁ hρ₂, by positivity, ?_⟩
  intro ρ h0 h1 x z hz y hy w hw
  have e1 := hb₁ ρ h0 (h1.trans (min_le_left _ _)) x z hz y hy w hw
  have e2 := hb₂ ρ h0 (h1.trans (min_le_right _ _)) x z hz y hy w hw
  have hp : 0 ≤ ρ ^ μ := Real.rpow_nonneg h0.le _
  calc |(c₁ * F y + c₂ * G y) - (c₁ * F w + c₂ * G w)|
      = |c₁ * (F y - F w) + c₂ * (G y - G w)| := by ring_nf
    _ ≤ |c₁ * (F y - F w)| + |c₂ * (G y - G w)| := abs_add_le _ _
    _ = |c₁| * |F y - F w| + |c₂| * |G y - G w| := by rw [abs_mul, abs_mul]
    _ ≤ |c₁| * (M₁ * ρ ^ μ) + |c₂| * (M₂ * ρ ^ μ) := by
        gcongr
    _ = (|c₁| * M₁ + |c₂| * M₂) * ρ ^ μ := by ring

/-- First derivatives of a linear combination on an open set. -/
lemma fderiv_lin {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) {F G : (EuclideanSpace ℝ (Fin d)) → ℝ} (hF : ContDiffOn ℝ 2 F U)
    (hG : ContDiffOn ℝ 2 G U) (c₁ c₂ : ℝ) {y : (EuclideanSpace ℝ (Fin d))} (hy : y ∈ U) :
    fderiv ℝ (fun y => c₁ * F y + c₂ * G y) y = c₁ • fderiv ℝ F y + c₂ • fderiv ℝ G y := by
  have dF : DifferentiableAt ℝ F y :=
    (hF.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hy)
  have dG : DifferentiableAt ℝ G y :=
    (hG.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hy)
  rw [fderiv_fun_add (dF.const_mul c₁) (dG.const_mul c₂), fderiv_const_mul dF,
    fderiv_const_mul dG]

/-- Second partials of a linear combination on an open set. -/
lemma partial2_lin {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) {F G : (EuclideanSpace ℝ (Fin d)) → ℝ} (hF : ContDiffOn ℝ 2 F U)
    (hG : ContDiffOn ℝ 2 G U) (c₁ c₂ : ℝ) {x : (EuclideanSpace ℝ (Fin d))} (hx : x ∈ U) (i j : Fin d) :
    fderiv ℝ (fun y => fderiv ℝ (fun y => c₁ * F y + c₂ * G y) y
      (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1)
      = c₁ * fderiv ℝ (fun y => fderiv ℝ F y (EuclideanSpace.single j 1)) x
          (EuclideanSpace.single i 1)
        + c₂ * fderiv ℝ (fun y => fderiv ℝ G y (EuclideanSpace.single j 1)) x
          (EuclideanSpace.single i 1) := by
  have DF : DifferentiableAt ℝ (fderiv ℝ F) x :=
    ((hF.fderiv_of_isOpen hU (m := 1) (by norm_num)).differentiableOn
      (by norm_num)).differentiableAt (hU.mem_nhds hx)
  have DG : DifferentiableAt ℝ (fderiv ℝ G) x :=
    ((hG.fderiv_of_isOpen hU (m := 1) (by norm_num)).differentiableOn
      (by norm_num)).differentiableAt (hU.mem_nhds hx)
  have hev : (fun y => fderiv ℝ (fun y => c₁ * F y + c₂ * G y) y (EuclideanSpace.single j 1))
      =ᶠ[𝓝 x] (fun y => c₁ * fderiv ℝ F y (EuclideanSpace.single j 1)
        + c₂ * fderiv ℝ G y (EuclideanSpace.single j 1)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [fderiv_lin hU hF hG c₁ c₂ hy]
    simp
  rw [hev.fderiv_eq]
  have dFj : DifferentiableAt ℝ (fun y => fderiv ℝ F y (EuclideanSpace.single j 1)) x :=
    DF.clm_apply (differentiableAt_const _)
  have dGj : DifferentiableAt ℝ (fun y => fderiv ℝ G y (EuclideanSpace.single j 1)) x :=
    DG.clm_apply (differentiableAt_const _)
  rw [fderiv_fun_add (dFj.const_mul c₁) (dGj.const_mul c₂), fderiv_const_mul dFj,
    fderiv_const_mul dGj]
  simp

/-- The exact graph is closed under linear combinations. -/
lemma graph_lin {Ω : Set (EuclideanSpace ℝ (Fin d))} (hopen : IsOpen Ω) {μ : ℝ} (hμ : 0 < μ)
    {a : (EuclideanSpace ℝ (Fin d)) → Matrix (Fin d) (Fin d) ℝ} {b c : (EuclideanSpace ℝ (Fin d)) → (EuclideanSpace ℝ (Fin d))}
    {p q : ((closure Ω) →ᵇ ℝ) × ((closure Ω) →ᵇ ℝ)}
    (hp : p ∈ obliqueDiffusionGraph Ω μ a b c) (hq : q ∈ obliqueDiffusionGraph Ω μ a b c)
    (c₁ c₂ : ℝ) : c₁ • p + c₂ • q ∈ obliqueDiffusionGraph Ω μ a b c := by
  simp only [obliqueDiffusionGraph, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd] at hp hq ⊢
  obtain ⟨⟨hF, hF2⟩, hFg, J₁, hJ₁c, hJ₁Ω, hJ₁b⟩ := hp
  obtain ⟨⟨hG, hG2⟩, hGg, J₂, hJ₂c, hJ₂Ω, hJ₂b⟩ := hq
  rw [restr_lin, restr_lin]
  set F := closedRegionRestriction p.1
  set G := closedRegionRestriction q.1
  refine ⟨⟨(contDiffOn_const.mul hF).add (contDiffOn_const.mul hG), fun i j => ?_⟩, ?_, ?_⟩
  · exact compHolder_congr (compHolder_lin hμ (hF2 i j) (hG2 i j) c₁ c₂)
      (fun x hx => partial2_lin hopen hF hG c₁ c₂ hx i j)
  · intro x hx
    beta_reduce
    rw [hFg x hx, hGg x hx, fderiv_lin hopen hF hG c₁ c₂ hx]
    simp only [partial2_lin hopen hF hG c₁ c₂ hx, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
    simp only [mul_left_comm _ c₁, mul_left_comm _ c₂, ← Finset.mul_sum]
    ring
  · refine ⟨fun x => c₁ • J₁ x + c₂ • J₂ x, (hJ₁c.const_smul c₁).add (hJ₂c.const_smul c₂),
      fun x hx => ?_, fun x hx => ?_⟩
    · show c₁ • J₁ x + c₂ • J₂ x = _
      rw [hJ₁Ω x hx, hJ₂Ω x hx, fderiv_lin hopen hF hG c₁ c₂ hx]
    · simp [hJ₁b x hx, hJ₂b x hx]

lemma graph_zero {Ω : Set (EuclideanSpace ℝ (Fin d))} {μ : ℝ} {a : (EuclideanSpace ℝ (Fin d)) → Matrix (Fin d) (Fin d) ℝ} {b c : (EuclideanSpace ℝ (Fin d)) → (EuclideanSpace ℝ (Fin d))} :
    (0 : ((closure Ω) →ᵇ ℝ) × ((closure Ω) →ᵇ ℝ)) ∈ obliqueDiffusionGraph Ω μ a b c := by
  simp only [obliqueDiffusionGraph, Set.mem_ofPred_eq, Prod.fst_zero, Prod.snd_zero]
  rw [restr_zero]
  refine ⟨⟨contDiffOn_const, fun i j => ?_⟩, ?_, ⟨fun _ => 0, continuous_const,
    fun x _ => ?_, fun x _ => rfl⟩⟩
  · refine compHolder_congr (F := fun _ => 0) ⟨continuousOn_const, 1, 0, one_pos, le_rfl, ?_⟩ ?_
    · intro ρ _ _ x z _ y _ w _; simp
    · intro x _; simp
  · intro x _; simp
  · simp

/-- The exact graph as a submodule. -/
def graphSub {Ω : Set (EuclideanSpace ℝ (Fin d))} (hopen : IsOpen Ω) {μ : ℝ} (hμ : 0 < μ)
    (a : (EuclideanSpace ℝ (Fin d)) → Matrix (Fin d) (Fin d) ℝ) (b c : (EuclideanSpace ℝ (Fin d)) → (EuclideanSpace ℝ (Fin d))) :
    Submodule ℝ (((closure Ω) →ᵇ ℝ) × ((closure Ω) →ᵇ ℝ)) where
  carrier := obliqueDiffusionGraph Ω μ a b c
  add_mem' hp hq := by
    simpa using graph_lin hopen hμ hp hq 1 1
  zero_mem' := graph_zero
  smul_mem' r p hp := by
    simpa using graph_lin hopen hμ hp hp r 0

/-- Reduction glue: the abstract generation theorem (C1) plus domain density (C2) give the parent. -/
theorem glue (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) (hopen : IsOpen Ω) (μ : ℝ)
    (hμ : 0 < μ ∧ μ ≤ 1)
    (a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (b c : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (C1 : ∀ (A : Submodule ℝ (((closure Ω) →ᵇ ℝ) × ((closure Ω) →ᵇ ℝ))),
      IsClosed (A : Set (((closure Ω) →ᵇ ℝ) × ((closure Ω) →ᵇ ℝ))) →
      (∀ fg ∈ A, ∀ lam : ℝ, 0 < lam → lam * ‖fg.1‖ ≤ ‖lam • fg.1 - fg.2‖) →
      (∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ h : (closure Ω) →ᵇ ℝ, ∀ delta : ℝ, 0 < delta →
        ∃ fg ∈ A, ‖(lam₀ • fg.1 - fg.2) - h‖ < delta) →
      (∀ h : (closure Ω) →ᵇ ℝ, ∀ delta : ℝ, 0 < delta → ∃ fg ∈ A, ‖fg.1 - h‖ < delta) →
      ∃ T : ℝ → ((closure Ω) →ᵇ ℝ) →L[ℝ] ((closure Ω) →ᵇ ℝ),
        IsStronglyContinuousContractionSemigroup T ∧
        (∀ f g, Tendsto (fun t : ℝ => t⁻¹ • (T t f - f))
          (𝓝[>] (0 : ℝ)) (𝓝 g) ↔ (f, g) ∈ A))
    (C2 : ∀ h : (closure Ω) →ᵇ ℝ, ∀ delta : ℝ, 0 < delta →
      ∃ fg ∈ obliqueDiffusionGraph Ω μ a b c, ‖fg.1 - h‖ < delta)
    (hest : ∀ fg ∈ closure (obliqueDiffusionGraph Ω μ a b c),
      ∀ lam : ℝ, 0 < lam → lam * ‖fg.1‖ ≤ ‖lam • fg.1 - fg.2‖)
    (hrange : ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ h : (closure Ω) →ᵇ ℝ, ∀ delta : ℝ,
      0 < delta → ∃ fg ∈ closure (obliqueDiffusionGraph Ω μ a b c),
        ‖(lam₀ • fg.1 - fg.2) - h‖ < delta) :
    let A := closure (obliqueDiffusionGraph Ω μ a b c)
    ∃ T : ℝ → ((closure Ω) →ᵇ ℝ) →L[ℝ] ((closure Ω) →ᵇ ℝ),
      IsStronglyContinuousContractionSemigroup T ∧
      (∀ f g, Tendsto (fun t : ℝ => t⁻¹ • (T t f - f))
        (𝓝[>] (0 : ℝ)) (𝓝 g) ↔ (f, g) ∈ A) := by
  intro A
  set S := graphSub hopen hμ.1 a b c with hS
  have hcoe : ((S.topologicalClosure : Submodule ℝ _) : Set _) = A := by
    rw [Submodule.topologicalClosure_coe]; rfl
  have hmem : ∀ p, p ∈ S.topologicalClosure ↔ p ∈ A := fun p => by
    rw [← hcoe]; rfl
  obtain ⟨T, hT, hgen⟩ := C1 S.topologicalClosure (Submodule.isClosed_topologicalClosure S)
    (fun fg hfg => hest fg ((hmem fg).1 hfg))
    (by
      obtain ⟨l, hl, hr⟩ := hrange
      exact ⟨l, hl, fun h δ hδ => by
        obtain ⟨fg, hfg, hn⟩ := hr h δ hδ
        exact ⟨fg, (hmem fg).2 hfg, hn⟩⟩)
    (fun h δ hδ => by
      obtain ⟨fg, hfg, hn⟩ := C2 h δ hδ
      exact ⟨fg, (hmem fg).2 (subset_closure hfg), hn⟩)
  exact ⟨T, hT, fun f g => (hgen f g).trans (hmem _)⟩


/-! ## C2d: assembly of the dense domain from the local correctors -/

lemma ctwice_congr {Ω : Set (EuclideanSpace ℝ (Fin d))} (hopen : IsOpen Ω) {μ : ℝ}
    {F G : EuclideanSpace ℝ (Fin d) → ℝ} (hF : CTwiceHolder Ω μ F)
    (h : ∀ x ∈ Ω, G x = F x) : CTwiceHolder Ω μ G := by
  refine ⟨hF.1.congr h, fun i j => compHolder_congr (hF.2 i j) (fun x hx => ?_)⟩
  have hd : ∀ y ∈ Ω, fderiv ℝ G y = fderiv ℝ F y := fun y hy => by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hopen.mem_nhds hy] with z hz
    exact h z hz
  have hev : (fun y => fderiv ℝ G y (EuclideanSpace.single j 1)) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ F y (EuclideanSpace.single j 1)) := by
    filter_upwards [hopen.mem_nhds hx] with z hz
    rw [hd z hz]
  rw [hev.fderiv_eq]

lemma ctwice_lin {Ω : Set (EuclideanSpace ℝ (Fin d))} (hopen : IsOpen Ω) {μ : ℝ} (hμ : 0 < μ)
    {F G : EuclideanSpace ℝ (Fin d) → ℝ} (hF : CTwiceHolder Ω μ F) (hG : CTwiceHolder Ω μ G)
    (c₁ c₂ : ℝ) : CTwiceHolder Ω μ (fun x => c₁ * F x + c₂ * G x) :=
  ⟨(contDiffOn_const.mul hF.1).add (contDiffOn_const.mul hG.1), fun i j =>
    compHolder_congr (compHolder_lin hμ (hF.2 i j) (hG.2 i j) c₁ c₂)
      (fun x hx => partial2_lin hopen hF.1 hG.1 c₁ c₂ hx i j)⟩

lemma ctwice_add {Ω : Set (EuclideanSpace ℝ (Fin d))} (hopen : IsOpen Ω) {μ : ℝ} (hμ : 0 < μ)
    {F G : EuclideanSpace ℝ (Fin d) → ℝ} (hF : CTwiceHolder Ω μ F) (hG : CTwiceHolder Ω μ G) :
    CTwiceHolder Ω μ (fun x => F x + G x) := by
  have := ctwice_lin hopen hμ hF hG 1 1
  simp only [one_mul] at this
  exact this

lemma ctwice_zero {Ω : Set (EuclideanSpace ℝ (Fin d))} {μ : ℝ} :
    CTwiceHolder Ω μ (fun _ => (0 : ℝ)) := by
  refine ⟨contDiffOn_const, fun i j => ?_⟩
  refine compHolder_congr (F := fun _ => 0) ⟨continuousOn_const, 1, 0, one_pos, le_rfl, ?_⟩ ?_
  · intro ρ _ _ x z _ y _ w _; simp
  · intro x _; simp

lemma ctwice_sum {Ω : Set (EuclideanSpace ℝ (Fin d))} (hopen : IsOpen Ω) {μ : ℝ} (hμ : 0 < μ)
    {ι : Type*} (s : Finset ι) (V : ι → EuclideanSpace ℝ (Fin d) → ℝ)
    (hV : ∀ i ∈ s, CTwiceHolder Ω μ (V i)) :
    CTwiceHolder Ω μ (fun x => ∑ i ∈ s, V i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (ctwice_zero (Ω := Ω) (μ := μ))
  | insert a s ha ih =>
    have e : (fun x => ∑ i ∈ insert a s, V i x) = fun x => V a x + ∑ i ∈ s, V i x := by
      funext x; rw [Finset.sum_insert ha]
    rw [e]
    exact ctwice_add hopen hμ (hV a (Finset.mem_insert_self a s))
      (ih fun i hi => hV i (Finset.mem_insert_of_mem hi))

/-- A `C^1` function is `ComponentHolder` on a bounded set (it is Lipschitz there). -/
lemma compHolder_of_contDiff {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hbounded : Bornology.IsBounded Ω) {μ : ℝ} (hμ : 0 < μ ∧ μ ≤ 1)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : ContDiff ℝ 1 φ) : ComponentHolder Ω μ φ := by
  obtain ⟨R, hR⟩ := hbounded.subset_closedBall 0
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) R).exists_bound_of_continuousOn
    ((hφ.continuous_fderiv one_ne_zero).continuousOn)
  refine ⟨hφ.continuous.continuousOn, 1, 2 * max C 0, one_pos, by positivity, ?_⟩
  intro ρ h0 h1 x z hz y hy w hw
  have hy' := connectedComponentIn_subset _ _ hy
  have hw' := connectedComponentIn_subset _ _ hw
  have hL : ‖φ y - φ w‖ ≤ max C 0 * ‖y - w‖ :=
    (convex_closedBall (0 : EuclideanSpace ℝ (Fin d)) R).norm_image_sub_le_of_norm_fderiv_le
      (fun u _ => (hφ.differentiable one_ne_zero) u) (fun u hu => (hC u hu).trans (le_max_left _ _))
      (hR hw'.1) (hR hy'.1)
  have hyw : ‖y - w‖ ≤ 2 * ρ := by
    have a1 : dist y x < ρ := hy'.2
    have a2 : dist w x < ρ := hw'.2
    have := dist_triangle_right y w x
    rw [← dist_eq_norm]; linarith
  have hρμ : ρ ≤ ρ ^ μ := by
    have := Real.rpow_le_rpow_of_exponent_ge h0 h1 hμ.2
    simpa using this
  rw [Real.norm_eq_abs] at hL
  calc |φ y - φ w| ≤ max C 0 * ‖y - w‖ := hL
    _ ≤ max C 0 * (2 * ρ) := by gcongr
    _ ≤ max C 0 * (2 * ρ ^ μ) := by gcongr
    _ = 2 * max C 0 * ρ ^ μ := by ring

lemma ctwice_smooth {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hbounded : Bornology.IsBounded Ω) {μ : ℝ} (hμ : 0 < μ ∧ μ ≤ 1)
    {F : EuclideanSpace ℝ (Fin d) → ℝ} (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) :
    CTwiceHolder Ω μ F := by
  refine ⟨(hF.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn, fun i j => ?_⟩
  apply compHolder_of_contDiff hbounded hμ
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => fderiv ℝ F y (EuclideanSpace.single j 1)) :=
    (contDiff_infty_iff_fderiv.1 hF).2.clm_apply contDiff_const
  have h2 := (contDiff_infty_iff_fderiv.1 h1).2.clm_apply
    (contDiff_const (c := (EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin d))))
  exact h2.of_le (WithTop.coe_le_coe.mpr le_top)

lemma clm_expand (L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    L v = ∑ i, v i * L (EuclideanSpace.single i 1) := by
  have hv : v = ∑ i, v i • EuclideanSpace.single i (1 : ℝ) := by
    have := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.sum_repr v
    simpa using this.symm
  conv_lhs => rw [hv]
  simp [map_sum, map_smul, smul_eq_mul]

/-- C2: the first projection of the exact graph is dense, given the extension child (C2b) and
the local corrector child (C2e). -/
theorem dense_of (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hbounded : Bornology.IsBounded Ω) (hopen : IsOpen Ω) (μ : ℝ) (hμ : 0 < μ ∧ μ ≤ 1)
    (a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (b c : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (haHolder : ∀ i j, ComponentHolder Ω μ (fun x => a x i j))
    (hbHolder : ∀ i, ComponentHolder Ω μ (fun x => b x i))
    (hext : ∀ φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ, ComponentHolder Ω μ φ →
      ∃ ψ : (closure Ω) →ᵇ ℝ, ∀ x : closure Ω, (x : EuclideanSpace ℝ (Fin (n + 1))) ∈ Ω →
        ψ x = φ x)
    (hcorr : ∀ x₀ ∈ frontier Ω, ∃ ρ : ℝ, 0 < ρ ∧
      ∀ F ξ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F →
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ξ → tsupport ξ ⊆ Metric.ball x₀ ρ →
        ∀ δ : ℝ, 0 < δ →
          ∃ V : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
            ContDiff ℝ 1 V ∧ HasCompactSupport V ∧ (∀ x, |V x| ≤ δ) ∧
            CTwiceHolder Ω μ V ∧
            ∀ x ∈ frontier Ω, fderiv ℝ V x (c x) = -(ξ x * fderiv ℝ F x (c x))) :
    ∀ h : (closure Ω) →ᵇ ℝ, ∀ delta : ℝ, 0 < delta →
      ∃ fg ∈ obliqueDiffusionGraph Ω μ a b c, ‖fg.1 - h‖ < delta := by
  classical
  intro h δ hδ
  have hK : IsCompact (closure Ω) := hbounded.isCompact_closure
  haveI : CompactSpace (closure Ω) := isCompact_iff_compactSpace.mp hK
  choose ρ hρ hV using hcorr
  have hfc : IsCompact (frontier Ω) := hK.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨t, ht⟩ := hfc.elim_finite_subcover
    (fun p : frontier Ω => Metric.ball (p : EuclideanSpace ℝ (Fin (n + 1))) (ρ p p.2))
    (fun _ => Metric.isOpen_ball)
    (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, Metric.mem_ball_self (hρ x hx)⟩)
  let U : t → Set (EuclideanSpace ℝ (Fin (n + 1))) := fun k => Metric.ball (k.1 : EuclideanSpace ℝ (Fin (n + 1))) (ρ k.1 k.1.2)
  have hcov : frontier Ω ⊆ ⋃ k, U k := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (ht hx)
    exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, hxi⟩
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
    isClosed_frontier U (fun _ => Metric.isOpen_ball) hcov
  have hfs : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f k) := fun k =>
    contMDiff_iff_contDiff.mp ((f k).contMDiff)
  obtain ⟨F, hF, hFh⟩ := Pd67abb68C2.smooth_approx hK h (half_pos hδ)
  set N : ℕ := Fintype.card t with hN
  set δ' : ℝ := δ / (2 * (N + 1)) with hδ'
  have hδ'0 : 0 < δ' := by positivity
  choose V hV1 hV2 hV3 hV4 hV5 using fun k : t => hV k.1 k.1.2 F (f k) hF (hfs k) (hf k) δ' hδ'0
  set G : EuclideanSpace ℝ (Fin (n + 1)) → ℝ := fun x => F x + ∑ k, V k x with hG
  have hG1 : ContDiff ℝ 1 G :=
    (hF.of_le (WithTop.coe_le_coe.mpr le_top)).add (ContDiff.sum fun k _ => hV1 k)
  let f1 : (closure Ω) →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun x => G x, hG1.continuous.comp continuous_subtype_val⟩
  have hf1 : ∀ x ∈ closure Ω, closedRegionRestriction f1 x = G x := by
    intro x hx
    unfold closedRegionRestriction
    rw [dif_pos hx]
    rfl
  have hf1Ω : ∀ x ∈ Ω, closedRegionRestriction f1 x = G x := fun x hx => hf1 x (subset_closure hx)
  have hCT : CTwiceHolder Ω μ (closedRegionRestriction f1) :=
    ctwice_congr hopen (ctwice_add hopen hμ.1 (ctwice_smooth hbounded hμ hF)
      (ctwice_sum hopen hμ.1 Finset.univ V (fun k _ => hV4 k))) hf1Ω
  have hfd : ∀ x ∈ Ω, fderiv ℝ (closedRegionRestriction f1) x = fderiv ℝ G x := by
    intro x hx
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hopen.mem_nhds hx] with z hz
    exact hf1Ω z hz
  let J : (closure Ω) → (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ) := fun x => fderiv ℝ G x
  have hJc : Continuous J := (hG1.continuous_fderiv one_ne_zero).comp continuous_subtype_val
  have hJb : ∀ x : closure Ω, (x : EuclideanSpace ℝ (Fin (n + 1))) ∈ frontier Ω →
      J x (c x) = 0 := by
    intro x hx
    have dF : DifferentiableAt ℝ F x := (hF.differentiable (by simp)) x
    have dV : ∀ k ∈ (Finset.univ : Finset t), DifferentiableAt ℝ (V k) x :=
      fun k _ => (hV1 k).differentiable one_ne_zero x
    show fderiv ℝ (fun x => F x + ∑ k, V k x) x (c x) = 0
    rw [fderiv_fun_add dF (DifferentiableAt.fun_sum dV), fderiv_fun_sum dV]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply]
    rw [Finset.sum_congr rfl (fun k _ => hV5 k x hx)]
    have hs := f.sum_eq_one hx
    rw [finsum_eq_sum_of_fintype] at hs
    rw [Finset.sum_neg_distrib, ← Finset.sum_mul, hs]
    ring
  -- second coordinate
  choose ψa hψa using fun i j => hext _ (haHolder i j)
  choose ψb hψb using fun i => hext _ (hbHolder i)
  choose ψf hψf using fun i j => hext _ (hCT.2 i j)
  let Jb : Fin (n + 1) → (closure Ω) →ᵇ ℝ := fun i => BoundedContinuousFunction.mkOfCompact
    ⟨fun x => J x (EuclideanSpace.single i 1), hJc.clm_apply continuous_const⟩
  let g : (closure Ω) →ᵇ ℝ :=
    (1 / 2 : ℝ) • (∑ i, ∑ j, ψa i j * ψf i j) + ∑ i, ψb i * Jb i
  refine ⟨(f1, g), ?_, ?_⟩
  · simp only [obliqueDiffusionGraph, Set.mem_ofPred_eq]
    refine ⟨hCT, ?_, J, hJc, fun x hx => (hfd x hx).symm, hJb⟩
    intro x hx
    have hxc : x ∈ closure Ω := subset_closure hx
    have hg : closedRegionRestriction g x = g ⟨x, hxc⟩ := by
      unfold closedRegionRestriction; rw [dif_pos hxc]
    rw [hg, clm_expand (fderiv ℝ (closedRegionRestriction f1) x) (b x), hfd x hx]
    simp only [g, BoundedContinuousFunction.coe_add, BoundedContinuousFunction.coe_smul,
      BoundedContinuousFunction.coe_sum, BoundedContinuousFunction.coe_mul, Pi.add_apply,
      Finset.sum_apply, Pi.mul_apply, smul_eq_mul]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [hψa i j ⟨x, hxc⟩ hx, hψf i j ⟨x, hxc⟩ hx]]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hψb i ⟨x, hxc⟩ hx]
    rfl
  · show ‖f1 - h‖ < δ
    rw [BoundedContinuousFunction.norm_lt_iff_of_compact hδ]
    intro x
    have e : (f1 - h) x = (F x - h x) + ∑ k, V k x := by
      show G x - h x = _
      simp only [hG]; ring
    rw [e, Real.norm_eq_abs]
    have hsum : |∑ k, V k (x : EuclideanSpace ℝ (Fin (n + 1)))| ≤ N * δ' := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun k _ => hV3 k x).trans ?_
      simp [hN]
    have hNδ : (N : ℝ) * δ' ≤ δ / 2 := by
      rw [hδ', mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have := hFh x
    calc |F x - h x + ∑ k, V k x| ≤ |F x - h x| + |∑ k, V k x| := abs_add_le _ _
      _ < δ / 2 + δ / 2 := by linarith
      _ = δ := by ring

end Pd67abb68

open EthierKurtz in
theorem solution (n : ℕ) (hd : 2 ≤ n + 1)
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hbounded : Bornology.IsBounded Ω) (hconnected : IsConnected Ω)
    (hopen : IsOpen Ω) (μ : ℝ) (hμ : 0 < μ ∧ μ ≤ 1)
    (hboundary : BoundaryCTwiceHolder Ω μ)
    (a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (b c normal : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (ha : ∀ x ∈ Ω, (a x).PosSemidef)
    (haHolder : ∀ i j, ComponentHolder Ω μ (fun x => a x i j))
    (hbHolder : ∀ i, ComponentHolder Ω μ (fun x => b x i))
    (helliptic : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ Ω,
      ∀ θ : EuclideanSpace ℝ (Fin (n + 1)), ‖θ‖ = 1 →
        ε ≤ ∑ i, ∑ j, θ i * a x i j * θ j)
    (hc : ∀ i, BoundaryCOnceHolder Ω μ (fun x => c x i))
    (hnormal : ∀ x ∈ frontier Ω, IsOutwardUnitNormal Ω x (normal x))
    (hoblique : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ frontier Ω,
      ε ≤ ∑ i, c x i * normal x i)
    (hest : ∀ fg ∈ closure (obliqueDiffusionGraph Ω μ a b c),
      ∀ lam : ℝ, 0 < lam → lam * ‖fg.1‖ ≤ ‖lam • fg.1 - fg.2‖)
    (hrange : ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ h : (closure Ω) →ᵇ ℝ, ∀ delta : ℝ,
      0 < delta → ∃ fg ∈ closure (obliqueDiffusionGraph Ω μ a b c),
        ‖(lam₀ • fg.1 - fg.2) - h‖ < delta) :
    let A := closure (obliqueDiffusionGraph Ω μ a b c)
    ∃ T : ℝ → ((closure Ω) →ᵇ ℝ) →L[ℝ] ((closure Ω) →ᵇ ℝ),
      IsStronglyContinuousContractionSemigroup T ∧
      (∀ f g, Tendsto (fun t : ℝ => t⁻¹ • (T t f - f))
        (𝓝[>] (0 : ℝ)) (𝓝 g) ↔ (f, g) ∈ A) := by
  exact Pd67abb68.glue n Ω hopen μ hμ a b c
    (fun A hA h1 h2 h3 => EthierKurtz.hille_yosida_closed_dissipative_relation A hA h1 h2 h3)
    (Pd67abb68.dense_of n Ω hbounded hopen μ hμ a b c haHolder hbHolder
      (fun φ hφ => EthierKurtz.componentHolder_extends_closure n Ω hbounded hopen μ hμ.1 normal
        hnormal φ hφ)
      (EthierKurtz.oblique_local_corrector n Ω hopen μ hμ c normal hc hnormal hoblique
        (fun q hq hqs hqH δ hδ => EthierKurtz.oblique_flat_lift n μ hμ q hq hqs hqH δ hδ)))
    hest hrange
