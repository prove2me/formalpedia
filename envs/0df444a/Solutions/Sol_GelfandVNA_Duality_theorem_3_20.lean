-- Prove2me | solution 1 for GelfandVNA.Duality.theorem_3_20
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T05:47:46.616121+00:00
-- url     : https://prove2.me/submissions/9b68cd15-4bb9-454f-809b-6e3c131b8e81

import Mathlib
import Definitions.Def_GelfandVNA_Duality_Locales
import Definitions.Def_GelfandVNA_Duality_VNA

/- Source module Work.Gelfand320.NormalValuationSpace; SHA256 ec6599262c1c2ed8e8d06fa3c0431beeb4a02e24a70de25ea1c20e75ba1bd385. -/
section Gelfand320WholeSource0

set_option autoImplicit false
namespace Gelfand320
open Set Filter
open QAlgorithms.Papers.Independent.Support21.P20
open scoped Topology
noncomputable section
universe u v
variable {A : Type u} [NormedAddCommGroup A] [NormedSpace ℂ A]
variable {B : Type v} [CompleteBooleanAlgebra B]

/-- Functionals whose values on the specified Boolean generators are continuous valuations. -/
def valuationFunctionals (k : B → A) : Submodule ℂ (A →L[ℂ] ℂ) where
  carrier := {Φ | IsContinuousValuation (fun p => Φ (k p))}
  zero_mem' := by
    refine ⟨⟨by simp, fun _ _ => by simp⟩, ?_⟩
    intro s a hs hd ha
    exact tendsto_const_nhds
  add_mem' := by
    intro Φ Ψ hΦ hΨ
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change Φ (k ⊥) + Ψ (k ⊥) = 0
      rw [show Φ (k ⊥) = 0 from hΦ.1.1, show Ψ (k ⊥) = 0 from hΨ.1.1, add_zero]
    · intro p q
      change (Φ (k p) + Ψ (k p)) + (Φ (k q) + Ψ (k q)) =
        (Φ (k (p ⊔ q)) + Ψ (k (p ⊔ q))) + (Φ (k (p ⊓ q)) + Ψ (k (p ⊓ q)))
      linear_combination hΦ.1.2 p q + hΨ.1.2 p q
    · intro s a hs hd ha
      exact (hΦ.2 s a hs hd ha).add (hΨ.2 s a hs hd ha)
  smul_mem' := by
    intro c Φ hΦ
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change c * Φ (k ⊥) = 0
      rw [show Φ (k ⊥) = 0 from hΦ.1.1, mul_zero]
    · intro p q
      change c * Φ (k p) + c * Φ (k q) = c * Φ (k (p ⊔ q)) + c * Φ (k (p ⊓ q))
      linear_combination c * hΦ.1.2 p q
    · intro s a hs hd ha
      exact (hΦ.2 s a hs hd ha).const_mul c

/-- Uniformly bounded Boolean generators make normal-valuation restrictions closed
in the operator norm. This supplies completeness of the candidate predual. -/
theorem valuationFunctionals_isClosed (k : B → A) (hk : ∀ p, ‖k p‖ ≤ 1) :
    IsClosed (valuationFunctionals k : Set (A →L[ℂ] ℂ)) := by
  apply IsSeqClosed.isClosed
  intro Φ Ψ hΦ hlim
  change ∀ n, IsContinuousValuation (fun p => Φ n (k p)) at hΦ
  change IsContinuousValuation (fun p => Ψ (k p))
  have ht (p : B) : Tendsto (fun n => Φ n (k p)) atTop (𝓝 (Ψ (k p))) := by
    have hc : Continuous (fun F : A →L[ℂ] ℂ => F (k p)) := by fun_prop
    exact (hc.tendsto Ψ).comp hlim
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hz : (fun n => Φ n (k ⊥)) = fun _ => (0 : ℂ) := funext (fun n => (hΦ n).1.1)
    exact tendsto_nhds_unique (ht ⊥) (by rw [hz]; exact tendsto_const_nhds)
  · intro p q
    have he : (fun n => Φ n (k p) + Φ n (k q)) =
        fun n => Φ n (k (p ⊔ q)) + Φ n (k (p ⊓ q)) := funext (fun n => (hΦ n).1.2 p q)
    have hl := (ht p).add (ht q)
    rw [he] at hl
    exact tendsto_nhds_unique hl ((ht (p ⊔ q)).add (ht (p ⊓ q)))
  · intro s a hs hd ha
    apply Metric.tendsto_nhds.2
    intro ε hε
    have hthird : 0 < ε / 3 := by positivity
    obtain ⟨n, hn⟩ := ((Metric.tendsto_nhds.1 hlim) (ε / 3) hthird).exists
    have hdist (p : B) : dist (Ψ (k p)) (Φ n (k p)) < ε / 3 := by
      rw [dist_eq_norm, ← ContinuousLinearMap.sub_apply]
      calc
        ‖(Ψ - Φ n) (k p)‖ ≤ ‖Ψ - Φ n‖ * ‖k p‖ := (Ψ - Φ n).le_opNorm _
        _ ≤ ‖Ψ - Φ n‖ := by simpa only [mul_one] using
          mul_le_mul_of_nonneg_left (hk p) (norm_nonneg _)
        _ < ε / 3 := by simpa only [dist_eq_norm, norm_sub_rev] using hn
    filter_upwards [(Metric.tendsto_nhds.1 ((hΦ n).2 s a hs hd ha)) (ε / 3) hthird] with p hp
    calc
      dist (Ψ (k p.val)) (Ψ (k a)) ≤ dist (Ψ (k p.val)) (Φ n (k p.val)) +
          dist (Φ n (k p.val)) (Φ n (k a)) + dist (Φ n (k a)) (Ψ (k a)) :=
        dist_triangle4 _ _ _ _
      _ < ε / 3 + ε / 3 + ε / 3 := by
        exact add_lt_add (add_lt_add (hdist p.val) hp) (by simpa only [dist_comm] using hdist a)
      _ = ε := by ring

end
end Gelfand320
end Gelfand320WholeSource0

/- Source module Work.Gelfand272.BooleanSpectrum; SHA256 dce2d0728a0f71594a5b259661781c7e374d0f39b82080d03e30e41adb05b027. -/
section Gelfand320WholeSource1

set_option autoImplicit false
namespace Gelfand272Spectrum
open TopologicalSpace
universe u
variable (B : Type u) [BooleanAlgebra B]

def idempotentIso : B ≃o {r : AsBoolRing B // IsIdempotentElem r} where
  toFun b := ⟨toBoolRing b,BooleanRing.isIdempotentElem _⟩
  invFun r := ofBoolRing r.val
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl
  map_rel_iff' := by
    intro a b
    change a ⊓ b = a ↔ a ≤ b
    exact inf_eq_left

noncomputable def clopensIso : B ≃o Clopens (PrimeSpectrum (AsBoolRing B)) :=
  (idempotentIso B).trans PrimeSpectrum.isIdempotentElemEquivClopens

noncomputable def basis (b : B) : Opens (PrimeSpectrum (AsBoolRing B)) :=
  (clopensIso B b).toOpens

theorem basis_eq_basicOpen (b : B) : basis B b = PrimeSpectrum.basicOpen (toBoolRing b) := rfl

theorem basis_le_iff (a b : B) : basis B a ≤ basis B b ↔ a ≤ b := by
  change clopensIso B a ≤ clopensIso B b ↔ a ≤ b
  exact (clopensIso B).le_iff_le

noncomputable def basisEmbedding : B ↪o Opens (PrimeSpectrum (AsBoolRing B)) where
  toFun := basis B
  inj' := by
    intro a b h
    exact le_antisymm ((basis_le_iff B a b).mp h.le) ((basis_le_iff B b a).mp h.ge)
  map_rel_iff' := fun {a b} => basis_le_iff B a b

theorem basis_bot : basis B ⊥ = ⊥ := by
  change (clopensIso B ⊥).toOpens = ⊥
  rw [map_bot]
  rfl

theorem basis_sup (a b : B) : basis B (a ⊔ b) = basis B a ⊔ basis B b := by
  change (clopensIso B (a ⊔ b)).toOpens = _
  rw [map_sup]
  rfl

theorem basis_compact (b : B) : IsCompactElement (basis B b) := by
  rw [basis_eq_basicOpen,Opens.isCompactElement_iff]
  exact PrimeSpectrum.isCompact_basicOpen _

theorem basis_density (U : Opens (PrimeSpectrum (AsBoolRing B))) :
    U = sSup (basis B '' {b | basis B b ≤ U}) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨V,⟨r,rfl⟩,hxV,hVU⟩ :=
      (Opens.isBasis_iff_nbhd.mp (PrimeSpectrum.isBasis_basic_opens (R := AsBoolRing B))) hx
    have he : basis B (ofBoolRing r) = PrimeSpectrum.basicOpen r := by
      rw [basis_eq_basicOpen,toBoolRing_ofBoolRing]
    have hm : basis B (ofBoolRing r) ∈ basis B '' {b | basis B b ≤ U} := by
      refine ⟨ofBoolRing r,?_,rfl⟩
      change basis B (ofBoolRing r) ≤ U
      simpa only [he] using hVU
    exact (le_sSup hm) (by simpa only [he] using hxV)
  · apply sSup_le
    rintro _ ⟨b,hb,rfl⟩
    exact hb

end Gelfand272Spectrum
end Gelfand320WholeSource1

/- Source module Work.Gelfand320.StepProjections; SHA256 411c371ce3b5e3e7b7e59d9d2e4fe5eb6358929164d518ae6adbbbeb910268ec. -/
section Gelfand320WholeSource2

set_option autoImplicit false
namespace Gelfand320
open Set TopologicalSpace GelfandVNA.Duality
noncomputable section
universe u
variable {K : Type u} [TopologicalSpace K] [CompactSpace K]

/-- Characteristic functions of clopen sets are continuous projections. -/
def clopenIndicator (U : Clopens K) : C(K, ℂ) :=
  ⟨(U : Set K).indicator (fun _ => 1), U.isClopen.continuous_indicator continuous_const⟩

def clopenProjection (U : Clopens K) : ProjAlg C(K, ℂ) :=
  ⟨⟨clopenIndicator U, by
      ext x
      by_cases hx : x ∈ U <;> simp [clopenIndicator, hx]⟩,
    by
      ext x
      by_cases hx : x ∈ U <;> simp [clopenIndicator, hx]⟩

lemma projection_point_zero_or_one (p : ProjAlg C(K, ℂ)) (x : K) :
    p.val x = 0 ∨ p.val x = 1 := by
  have he : p.val x * p.val x = p.val x := congrArg (fun f : C(K, ℂ) => f x) p.isStarProjection.1
  have hz : p.val x * (p.val x - 1) = 0 := by linear_combination he
  rcases mul_eq_zero.mp hz with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

def projectionClopen (p : ProjAlg C(K, ℂ)) : Clopens K where
  carrier := {x | p.val x = 1}
  isClopen' := by
    refine ⟨isClosed_eq p.val.continuous continuous_const, ?_⟩
    have he : {x | p.val x = 1} = {x | p.val x = 0}ᶜ := by
      ext x
      rcases projection_point_zero_or_one p x with hx | hx <;> simp [hx]
    rw [he]
    exact (isClosed_eq p.val.continuous continuous_const).isOpen_compl

/-- The Boolean algebra of projections of C(K) is exactly the algebra of clopen sets. -/
def clopenProjectionIso : Clopens K ≃o ProjAlg C(K, ℂ) where
  toFun := clopenProjection
  invFun := projectionClopen
  left_inv U := by
    apply Clopens.ext
    ext x
    by_cases hx : x ∈ U <;> simp [projectionClopen, clopenProjection, clopenIndicator, ProjAlg.val, hx]
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    ext x
    change ({y | p.val y = 1}.indicator (fun _ => (1 : ℂ))) x = p.val x
    rcases projection_point_zero_or_one p x with hx | hx <;> simp [hx]
  map_rel_iff' := by
    intro U V
    change clopenIndicator U * clopenIndicator V = clopenIndicator U ↔ U ≤ V
    constructor
    · intro h x hx
      have he := congrArg (fun f : C(K, ℂ) => f x) h
      by_contra hn
      simpa [clopenIndicator, hx, hn] using he
    · intro h
      ext x
      by_cases hx : x ∈ U
      · simp [clopenIndicator, hx, h hx]
      · simp [clopenIndicator, hx]

/-- The Stone step algebra already has the required projection algebra;
its Banach predual is constructed separately. -/
def booleanProjectionIso (B : Type u) [BooleanAlgebra B] :
    B ≃o ProjAlg C(PrimeSpectrum (AsBoolRing B), ℂ) :=
  (Gelfand272Spectrum.clopensIso B).trans clopenProjectionIso

end
end Gelfand320
end Gelfand320WholeSource2

/- Source module Work.Gelfand39BoundedExtension; SHA256 65767134f0cf12786a5ab77bbad9999be1b947e9d99e54eedc8bea3a86e68091. -/
section Gelfand320WholeSource3


set_option autoImplicit false


namespace Gelfand38

open WeakDual

lemma complex_real_unit_iff (z : ℂ) :
    (z.im = 0 ∧ ‖z‖ ≤ 1) ↔
      ∀ t : ℝ, ‖z + (t : ℂ) * Complex.I‖ ≤ Real.sqrt (1 + t ^ 2) := by
  have hs (t : ℝ) : ‖z + (t : ℂ) * Complex.I‖ ^ 2 =
      z.re ^ 2 + (z.im + t) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, sub_self, add_zero,
      Complex.add_im, Complex.mul_im, mul_one]
    ring
  constructor
  · rintro ⟨hi, hn⟩ t
    have hn2 : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
    have hz : z.re ^ 2 ≤ 1 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hi] at hn2
      nlinarith only [hn2]
    have hr := Real.sq_sqrt (show 0 ≤ 1 + t ^ 2 by positivity)
    have hns := hs t
    rw [hi, zero_add] at hns
    nlinarith [Real.sqrt_nonneg (1 + t ^ 2), norm_nonneg (z + (t : ℂ) * Complex.I)]
  · intro h
    have hi : z.im = 0 := by
      by_contra hne
      have hb := h z.im⁻¹
      have hr := Real.sq_sqrt (show 0 ≤ 1 + (z.im⁻¹) ^ 2 by positivity)
      have hn := norm_nonneg (z + (z.im⁻¹ : ℝ) * Complex.I)
      have hm : z.im * z.im⁻¹ = 1 := mul_inv_cancel₀ hne
      have hns := hs z.im⁻¹
      nlinarith [sq_nonneg z.re, sq_nonneg z.im]
    exact ⟨hi, by simpa using h 0⟩

variable {A : Type*} [CommCStarAlgebra A]

lemma gelfand_norm (a : A) : ‖gelfandTransform ℂ A a‖ = ‖a‖ :=
  (gelfandTransform_isometry A).norm_map_of_map_zero (map_zero _) a

lemma gelfand_selfAdjoint_iff (a : A) :
    IsSelfAdjoint a ↔ ∀ χ : characterSpace ℂ A, (gelfandTransform ℂ A a χ).im = 0 := by
  constructor
  · intro h χ
    have he := congrArg (fun f : C(characterSpace ℂ A, ℂ) => f χ)
      (show gelfandTransform ℂ A (star a) = gelfandTransform ℂ A a from congrArg _ h)
    rw [gelfandTransform_map_star] at he
    have hi := congrArg Complex.im he
    change -(gelfandTransform ℂ A a χ).im = (gelfandTransform ℂ A a χ).im at hi
    linarith
  · intro h
    apply (gelfandTransform_isometry A).injective
    rw [gelfandTransform_map_star]
    ext χ
    apply Complex.ext
    · rfl
    · change -(gelfandTransform ℂ A a χ).im = (gelfandTransform ℂ A a χ).im
      rw [h χ, neg_zero]

lemma selfAdjoint_unit_iff_norm_balls (a : A) :
    (IsSelfAdjoint a ∧ ‖a‖ ≤ 1) ↔
      ∀ t : ℝ, ‖a + ((t : ℂ) * Complex.I) • (1 : A)‖ ≤ Real.sqrt (1 + t ^ 2) := by
  have he (t : ℝ) (χ : characterSpace ℂ A) :
      gelfandTransform ℂ A (a + ((t : ℂ) * Complex.I) • (1 : A)) χ =
        gelfandTransform ℂ A a χ + (t : ℂ) * Complex.I := by
    simp
  constructor
  · rintro ⟨ha, hn⟩ t
    rw [← gelfand_norm]
    apply (ContinuousMap.norm_le _ (Real.sqrt_nonneg _)).2
    intro χ
    rw [he]
    apply (complex_real_unit_iff _).1
    refine ⟨(gelfand_selfAdjoint_iff a).1 ha χ, ?_⟩
    exact (ContinuousMap.norm_coe_le_norm _ χ).trans ((gelfand_norm a).trans_le hn)
  · intro h
    have hv (χ : characterSpace ℂ A) :
        (gelfandTransform ℂ A a χ).im = 0 ∧ ‖gelfandTransform ℂ A a χ‖ ≤ 1 := by
      apply (complex_real_unit_iff _).2
      intro t
      rw [← he t χ]
      exact (ContinuousMap.norm_coe_le_norm _ χ).trans
        ((gelfand_norm _).trans_le (h t))
    refine ⟨(gelfand_selfAdjoint_iff a).2 (fun χ => (hv χ).1), ?_⟩
    rw [← gelfand_norm]
    exact (ContinuousMap.norm_le _ zero_le_one).2 (fun χ => (hv χ).2)


def PositiveUnit (a : A) : Prop :=
  ∀ χ : characterSpace ℂ A,
    (gelfandTransform ℂ A a χ).im = 0 ∧
    0 ≤ (gelfandTransform ℂ A a χ).re ∧ (gelfandTransform ℂ A a χ).re ≤ 1

lemma complex_positive_unit_iff (z : ℂ) :
    (z.im = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1) ↔
      ((z + z - 1).im = 0 ∧ ‖z + z - 1‖ ≤ 1) := by
  have hi : (z + z - 1).im = 2 * z.im := by simp; ring
  have hn : ‖z + z - 1‖ ^ 2 = (2 * z.re - 1) ^ 2 + (2 * z.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.sub_im,
      Complex.add_im, Complex.one_im, sub_zero]
    ring
  constructor
  · rintro ⟨him, h0, h1⟩
    refine ⟨by rw [hi, him, mul_zero], ?_⟩
    rw [him, mul_zero, zero_pow (by decide), add_zero] at hn
    nlinarith [norm_nonneg (z + z - 1)]
  · rintro ⟨him, hnorm⟩
    have him0 : z.im = 0 := by rw [hi] at him; linarith
    refine ⟨him0, ?_, ?_⟩ <;>
      nlinarith [norm_nonneg (z + z - 1), sq_nonneg (2 * z.im)]

lemma positiveUnit_iff_center (a : A) :
    PositiveUnit a ↔ IsSelfAdjoint (a + a - 1) ∧ ‖a + a - 1‖ ≤ 1 := by
  have he (χ : characterSpace ℂ A) :
      gelfandTransform ℂ A (a + a - 1) χ =
        gelfandTransform ℂ A a χ + gelfandTransform ℂ A a χ - 1 := by simp
  constructor
  · intro h
    have hv (χ : characterSpace ℂ A) := (complex_positive_unit_iff _).1 (h χ)
    refine ⟨(gelfand_selfAdjoint_iff _).2 ?_, ?_⟩
    · intro χ
      rw [he]
      exact (hv χ).1
    · rw [← gelfand_norm]
      apply (ContinuousMap.norm_le _ zero_le_one).2
      intro χ
      rw [he]
      exact (hv χ).2
  · rintro ⟨ha, hn⟩ χ
    apply (complex_positive_unit_iff _).2
    rw [← he]
    exact ⟨(gelfand_selfAdjoint_iff _).1 ha χ,
      (ContinuousMap.norm_coe_le_norm _ χ).trans ((gelfand_norm _).trans_le hn)⟩

lemma positiveUnit_norm_le {a : A} (ha : PositiveUnit a) : ‖a‖ ≤ 1 := by
  rw [← gelfand_norm]
  apply (ContinuousMap.norm_le _ zero_le_one).2
  intro χ
  obtain ⟨hi, h0, h1⟩ := ha χ
  have hs := Complex.sq_norm (gelfandTransform ℂ A a χ)
  rw [Complex.normSq_apply, hi] at hs
  nlinarith [norm_nonneg (gelfandTransform ℂ A a χ)]

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

lemma isClosed_normBall (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (c : A) (r : ℝ) :
    IsClosed {w : WeakDual ℂ X | ‖e (WeakDual.toStrongDual w) - c‖ ≤ r} := by
  convert WeakDual.isClosed_closedBall (e.symm c) r using 1
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm]
  rw [← e.norm_map (WeakDual.toStrongDual w - e.symm c), map_sub, e.apply_symm_apply]

lemma isClosed_positiveUnit (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) :
    IsClosed {w : WeakDual ℂ X | PositiveUnit (e (WeakDual.toStrongDual w))} := by
  simp only [positiveUnit_iff_center, selfAdjoint_unit_iff_norm_balls, Set.ofPred_forall]
  apply isClosed_iInter
  intro t
  have hc := (isClosed_normBall e (1 - ((t : ℂ) * Complex.I) • (1 : A))
    (Real.sqrt (1 + t ^ 2))).preimage (continuous_id.add continuous_id)
  convert hc using 1
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  change (‖e (WeakDual.toStrongDual w) + e (WeakDual.toStrongDual w) - 1 +
    ((t : ℂ) * Complex.I) • (1 : A)‖ ≤ _) ↔
    (‖e (WeakDual.toStrongDual w + WeakDual.toStrongDual w) -
      (1 - ((t : ℂ) * Complex.I) • (1 : A))‖ ≤ _)
  rw [map_add]
  abel_nf

lemma isCompact_positiveUnit (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) :
    IsCompact {w : WeakDual ℂ X | PositiveUnit (e (WeakDual.toStrongDual w))} := by
  apply (WeakDual.isCompact_closedBall (0 : StrongDual ℂ X) 1).of_isClosed_subset
    (isClosed_positiveUnit e)
  intro w hw
  simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
  rw [← e.norm_map]
  exact positiveUnit_norm_le hw


def SpectralLE (a b : A) : Prop :=
  ∀ χ : characterSpace ℂ A,
    (gelfandTransform ℂ A a χ).re ≤ (gelfandTransform ℂ A b χ).re

lemma spectralLE_refl (a : A) : SpectralLE a a := fun _ => le_rfl

lemma spectralLE_trans {a b c : A} (hab : SpectralLE a b) (hbc : SpectralLE b c) :
    SpectralLE a c := fun χ => (hab χ).trans (hbc χ)

lemma spectralLE_antisymm {a b : A} (ha : PositiveUnit a) (hb : PositiveUnit b)
    (hab : SpectralLE a b) (hba : SpectralLE b a) : a = b := by
  apply (gelfandTransform_isometry A).injective
  ext χ
  apply Complex.ext
  · exact le_antisymm (hab χ) (hba χ)
  · exact (ha χ).1.trans (hb χ).1.symm

lemma positiveUnit_sub_iff {a b : A} (ha : PositiveUnit a) (hb : PositiveUnit b) :
    PositiveUnit (b - a) ↔ SpectralLE a b := by
  have he (χ : characterSpace ℂ A) :
      gelfandTransform ℂ A (b - a) χ =
        gelfandTransform ℂ A b χ - gelfandTransform ℂ A a χ := by simp
  constructor
  · intro h χ
    have ht := (h χ).2.1
    rw [he, Complex.sub_re] at ht
    linarith
  · intro h χ
    rw [he, Complex.sub_im, Complex.sub_re, (ha χ).1, (hb χ).1, sub_self]
    exact ⟨rfl, sub_nonneg.mpr (h χ), by linarith [(hb χ).2.2, (ha χ).2.1]⟩

lemma isClosed_positiveUnit_lower (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (p : A) (hp : PositiveUnit p) :
    IsClosed {w : WeakDual ℂ X |
      PositiveUnit (e (WeakDual.toStrongDual w)) ∧ SpectralLE p (e (WeakDual.toStrongDual w))} := by
  have ht := (isClosed_positiveUnit e).preimage
    (continuous_id.sub (continuous_const : Continuous (fun _ : WeakDual ℂ X =>
      StrongDual.toWeakDual (e.symm p))))
  have he : {w : WeakDual ℂ X | PositiveUnit (e (WeakDual.toStrongDual w)) ∧
      SpectralLE p (e (WeakDual.toStrongDual w))} =
      {w : WeakDual ℂ X | PositiveUnit (e (WeakDual.toStrongDual w))} ∩
      (fun w : WeakDual ℂ X => w - StrongDual.toWeakDual (e.symm p)) ⁻¹'
        {w : WeakDual ℂ X | PositiveUnit (e (WeakDual.toStrongDual w))} := by
    ext w
    change (_ ∧ _) ↔ (_ ∧ PositiveUnit (e (WeakDual.toStrongDual w - e.symm p)))
    rw [map_sub, e.apply_symm_apply]
    exact and_congr_right (fun hw => (positiveUnit_sub_iff hp hw).symm)
  rw [he]
  exact (isClosed_positiveUnit e).inter ht

lemma isClosed_positiveUnit_upper (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (p : A) (hp : PositiveUnit p) :
    IsClosed {w : WeakDual ℂ X |
      PositiveUnit (e (WeakDual.toStrongDual w)) ∧ SpectralLE (e (WeakDual.toStrongDual w)) p} := by
  have ht := (isClosed_positiveUnit e).preimage
    ((continuous_const : Continuous (fun _ : WeakDual ℂ X =>
      StrongDual.toWeakDual (e.symm p))).sub continuous_id)
  have he : {w : WeakDual ℂ X | PositiveUnit (e (WeakDual.toStrongDual w)) ∧
      SpectralLE (e (WeakDual.toStrongDual w)) p} =
      {w : WeakDual ℂ X | PositiveUnit (e (WeakDual.toStrongDual w))} ∩
      (fun w : WeakDual ℂ X => StrongDual.toWeakDual (e.symm p) - w) ⁻¹'
        {w : WeakDual ℂ X | PositiveUnit (e (WeakDual.toStrongDual w))} := by
    ext w
    change (_ ∧ _) ↔ (_ ∧ PositiveUnit (e (e.symm p - WeakDual.toStrongDual w)))
    rw [map_sub, e.apply_symm_apply]
    exact and_congr_right (fun hw => (positiveUnit_sub_iff hw hp).symm)
  rw [he]
  exact (isClosed_positiveUnit e).inter ht


end Gelfand38


namespace Gelfand38

open WeakDual Set

variable {A : Type*} [CommCStarAlgebra A]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem exists_positive_lub (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    {ι : Type*} [Nonempty ι] (f : ι → A) (hf : ∀ i, PositiveUnit (f i))
    (hd : Directed SpectralLE f) :
    ∃ a : A, PositiveUnit a ∧ (∀ i, SpectralLE (f i) a) ∧
      ∀ b : A, PositiveUnit b → (∀ i, SpectralLE (f i) b) → SpectralLE a b := by
  classical
  let lift : A → WeakDual ℂ X := fun a => StrongDual.toWeakDual (e.symm a)
  let eval : WeakDual ℂ X → A := fun w => e (WeakDual.toStrongDual w)
  have hlift (a : A) : eval (lift a) = a := e.apply_symm_apply a
  let K : Set (WeakDual ℂ X) := {w | PositiveUnit (eval w)}
  have hKc : IsCompact K := isCompact_positiveUnit e
  have hKcl : IsClosed K := isClosed_positiveUnit e
  let tail : ι → Set (WeakDual ℂ X) := fun i =>
    {w | ∃ j, SpectralLE (f i) (f j) ∧ w = lift (f j)}
  have htK (i : ι) : closure (tail i) ⊆ K := by
    apply closure_minimal _ hKcl
    rintro w ⟨j, hij, rfl⟩
    change PositiveUnit (eval (lift (f j)))
    rw [hlift]
    exact hf j
  have htd : Directed (· ⊇ ·) (fun i => closure (tail i)) := by
    intro i j
    obtain ⟨k, hik, hjk⟩ := hd i j
    refine ⟨k, closure_mono ?_, closure_mono ?_⟩
    · rintro w ⟨l, hkl, hw⟩
      exact ⟨l, spectralLE_trans hik hkl, hw⟩
    · rintro w ⟨l, hkl, hw⟩
      exact ⟨l, spectralLE_trans hjk hkl, hw⟩
  have htn (i : ι) : (closure (tail i)).Nonempty :=
    ⟨lift (f i), subset_closure ⟨i, spectralLE_refl _, rfl⟩⟩
  obtain ⟨w, hw⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    (fun i => closure (tail i)) htd htn
    (fun i => hKc.of_isClosed_subset isClosed_closure (htK i))
    (fun _ => isClosed_closure)
  have hw' : ∀ i, w ∈ closure (tail i) := mem_iInter.mp hw
  refine ⟨eval w, htK (Classical.arbitrary ι) (hw' _), ?_, ?_⟩
  · intro i
    have hc : closure (tail i) ⊆ {w | PositiveUnit (eval w) ∧ SpectralLE (f i) (eval w)} := by
      apply closure_minimal _ (isClosed_positiveUnit_lower e (f i) (hf i))
      rintro w ⟨j, hij, rfl⟩
      change PositiveUnit (eval (lift (f j))) ∧ SpectralLE (f i) (eval (lift (f j)))
      rw [hlift]
      exact ⟨hf j, hij⟩
    exact (hc (hw' i)).2
  · intro b hb hub
    have hc : closure (tail (Classical.arbitrary ι)) ⊆
        {w | PositiveUnit (eval w) ∧ SpectralLE (eval w) b} := by
      apply closure_minimal _ (isClosed_positiveUnit_upper e b hb)
      rintro w ⟨j, hij, rfl⟩
      change PositiveUnit (eval (lift (f j))) ∧ SpectralLE (eval (lift (f j))) b
      rw [hlift]
      exact ⟨hf j, hub j⟩
    exact (hc (hw' _)).2


end Gelfand38


namespace Gelfand38

open WeakDual GelfandVNA.Duality

variable {A : Type*} [CommCStarAlgebra A]

lemma projection_value_zero_or_one (p : ProjAlg A) (χ : characterSpace ℂ A) :
    gelfandTransform ℂ A p.val χ = 0 ∨ gelfandTransform ℂ A p.val χ = 1 := by
  apply IsIdempotentElem.iff_eq_zero_or_one.mp
  have h := congrArg (fun a : A => gelfandTransform ℂ A a χ) p.isStarProjection.1
  change gelfandTransform ℂ A p.val χ * gelfandTransform ℂ A p.val χ =
    gelfandTransform ℂ A p.val χ
  simpa only [map_mul, ContinuousMap.mul_apply] using h

lemma projection_positiveUnit (p : ProjAlg A) : PositiveUnit p.val := by
  intro χ
  rcases projection_value_zero_or_one p χ with h | h <;> simp [h]

lemma projection_le_iff (p q : ProjAlg A) :
    p ≤ q ↔ SpectralLE p.val q.val := by
  change p.val * q.val = p.val ↔ _
  constructor
  · intro h χ
    have hm := congrArg (fun a : A => gelfandTransform ℂ A a χ) h
    have hp := projection_value_zero_or_one p χ
    have hq := projection_value_zero_or_one q χ
    simp only [map_mul, ContinuousMap.mul_apply] at hm
    rcases hp with hp | hp <;> rcases hq with hq | hq <;> simp_all
  · intro h
    apply (gelfandTransform_isometry A).injective
    ext χ
    have hh := h χ
    have hp := projection_value_zero_or_one p χ
    have hq := projection_value_zero_or_one q χ
    simp only [map_mul, ContinuousMap.mul_apply]
    rcases hp with hp | hp <;> rcases hq with hq | hq <;> simp_all
    norm_num at *

lemma positiveUnit_square {a : A} (ha : PositiveUnit a) : PositiveUnit (a * a) := by
  intro χ
  obtain ⟨hi, h0, h1⟩ := ha χ
  simp only [map_mul, ContinuousMap.mul_apply, Complex.mul_im, Complex.mul_re,
    hi, mul_zero, zero_mul, add_zero, sub_zero]
  exact ⟨trivial, mul_self_nonneg _, by nlinarith⟩

lemma positiveUnit_square_le {a : A} (ha : PositiveUnit a) : SpectralLE (a * a) a := by
  intro χ
  obtain ⟨hi, h0, h1⟩ := ha χ
  simp only [map_mul, ContinuousMap.mul_apply, Complex.mul_re, hi, mul_zero, sub_zero]
  nlinarith

lemma projection_le_square (p : ProjAlg A) {a : A} (ha : PositiveUnit a)
    (hpa : SpectralLE p.val a) : SpectralLE p.val (a * a) := by
  intro χ
  obtain ⟨hi, h0, h1⟩ := ha χ
  have hp := hpa χ
  simp only [map_mul, ContinuousMap.mul_apply, Complex.mul_re, hi, mul_zero, sub_zero]
  rcases projection_value_zero_or_one p χ with he | he
  · rw [he, Complex.zero_re]
    exact mul_self_nonneg _
  · rw [he, Complex.one_re] at hp ⊢
    nlinarith

theorem projections_complete [WStarAlgebra A] (s : Set (ProjAlg A)) :
    ∃ p : ProjAlg A, IsLUB s p := by
  classical
  obtain ⟨X, hX, hN, hC, ⟨e⟩⟩ := WStarAlgebra.exists_predual (M := A)
  let f : Finset s → ProjAlg A := fun t => t.sup Subtype.val
  have hf : ∀ t : Finset s, PositiveUnit (f t).val := fun t => projection_positiveUnit (f t)
  have hd : Directed SpectralLE (fun t : Finset s => (f t).val) := by
    intro t u
    refine ⟨t ∪ u, (projection_le_iff _ _).1 ?_, (projection_le_iff _ _).1 ?_⟩
    · exact Finset.sup_mono Finset.subset_union_left
    · exact Finset.sup_mono Finset.subset_union_right
  obtain ⟨a, ha, hub, hleast⟩ := exists_positive_lub e (fun t => (f t).val) hf hd
  have haa : a * a = a := spectralLE_antisymm (positiveUnit_square ha) ha
    (positiveUnit_square_le ha)
    (hleast (a * a) (positiveUnit_square ha) (fun t => projection_le_square (f t) ha (hub t)))
  have hstar : IsSelfAdjoint a := (gelfand_selfAdjoint_iff a).2 (fun χ => (ha χ).1)
  let p : ProjAlg A := ⟨⟨a, haa⟩, hstar⟩
  refine ⟨p, ?_, ?_⟩
  · intro q hq
    apply (projection_le_iff q p).2
    change SpectralLE q.val a
    have hh := hub {⟨q, hq⟩}
    simpa [f] using hh
  · intro q hq
    apply (projection_le_iff p q).2
    apply hleast q.val (projection_positiveUnit q)
    intro t
    apply (projection_le_iff (f t) q).1
    exact Finset.sup_le (fun r hr => hq r.property)


end Gelfand38


open WeakDual

open GelfandVNA.Duality

universe u



set_option autoImplicit false

namespace Gelfand39Inverse

open Gelfand38 GelfandVNA.Duality WeakDual

noncomputable section

variable {A : Type*} [CommCStarAlgebra A]

def ramp (f : C(characterSpace ℂ A, ℝ)) (n : ℕ) : C(characterSpace ℂ A, ℂ) :=
  ⟨fun χ => (min ((n : ℝ) * max (f χ) 0) 1 : ℝ), by fun_prop⟩

def rampElement (f : C(characterSpace ℂ A, ℝ)) (n : ℕ) : A :=
  (gelfandStarTransform A).symm (ramp f n)

lemma ramp_eval (f : C(characterSpace ℂ A, ℝ)) (n : ℕ) (χ : characterSpace ℂ A) :
    gelfandTransform ℂ A (rampElement f n) χ =
      (min ((n : ℝ) * max (f χ) 0) 1 : ℝ) := by
  change gelfandStarTransform A ((gelfandStarTransform A).symm (ramp f n)) χ = _
  rw [StarAlgEquiv.apply_symm_apply]
  rfl

lemma ramp_positive (f : C(characterSpace ℂ A, ℝ)) (n : ℕ) :
    PositiveUnit (rampElement f n) := by
  intro χ
  rw [ramp_eval]
  exact ⟨rfl, le_min (mul_nonneg (Nat.cast_nonneg n) (le_max_right _ _)) zero_le_one,
    min_le_right _ _⟩

lemma ramp_monotone (f : C(characterSpace ℂ A, ℝ)) {n m : ℕ} (hnm : n ≤ m) :
    SpectralLE (rampElement f n) (rampElement f m) := by
  intro χ
  rw [ramp_eval, ramp_eval]
  exact min_le_min (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hnm) (le_max_right _ _)) le_rfl

theorem exists_support_projection [WStarAlgebra A] (f : C(characterSpace ℂ A, ℝ)) :
    ∃ p : ProjAlg A,
      (∀ χ : characterSpace ℂ A, 0 < f χ → gelfandTransform ℂ A p.val χ = 1) ∧
      (∀ n : ℕ, SpectralLE (rampElement f n) p.val) ∧
      ∀ b : A, PositiveUnit b → (∀ n : ℕ, SpectralLE (rampElement f n) b) →
        SpectralLE p.val b := by
  obtain ⟨X, hX, hN, hC, ⟨e⟩⟩ := WStarAlgebra.exists_predual (M := A)
  have hd : Directed SpectralLE (rampElement f) := by
    intro n m
    exact ⟨max n m, ramp_monotone f (le_max_left _ _), ramp_monotone f (le_max_right _ _)⟩
  obtain ⟨a, ha, hub, hleast⟩ := exists_positive_lub e (rampElement f) (ramp_positive f) hd
  have hone (χ : characterSpace ℂ A) (hχ : 0 < f χ) : gelfandTransform ℂ A a χ = 1 := by
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / f χ)
    have hlarge : 1 ≤ (n : ℝ) * max (f χ) 0 := by
      rw [max_eq_left hχ.le]
      exact (div_le_iff₀ hχ).mp hn.le
    have hu := hub n χ
    rw [ramp_eval] at hu
    change min ((n : ℝ) * max (f χ) 0) 1 ≤ (gelfandTransform ℂ A a χ).re at hu
    rw [min_eq_right hlarge] at hu
    apply Complex.ext
    · exact le_antisymm (ha χ).2.2 hu
    · exact (ha χ).1
  have hsq : ∀ n : ℕ, SpectralLE (rampElement f n) (a * a) := by
    intro n χ
    rw [ramp_eval]
    simp only [map_mul, ContinuousMap.mul_apply, Complex.mul_re, (ha χ).1,
      mul_zero, sub_zero, Complex.ofReal_re]
    by_cases hχ : f χ ≤ 0
    · rw [max_eq_right hχ, mul_zero, min_eq_left zero_le_one]
      exact mul_self_nonneg _
    · rw [hone χ (lt_of_not_ge hχ), Complex.one_re, mul_one]
      exact min_le_right _ _
  have haa : a * a = a := spectralLE_antisymm (positiveUnit_square ha) ha
    (positiveUnit_square_le ha) (hleast (a * a) (positiveUnit_square ha) hsq)
  let p : ProjAlg A := ⟨⟨a, haa⟩, (gelfand_selfAdjoint_iff a).2 (fun χ => (ha χ).1)⟩
  exact ⟨p, hone, hub, hleast⟩


end
end Gelfand39Inverse


set_option autoImplicit false

namespace Gelfand39Inverse

open Gelfand38 GelfandVNA.Duality WeakDual Set
open scoped Pointwise

variable {A : Type*} [CommCStarAlgebra A]

lemma inverse_eval (F : C(characterSpace ℂ A, ℂ)) (χ : characterSpace ℂ A) :
    gelfandTransform ℂ A ((gelfandStarTransform A).symm F) χ = F χ := by
  change gelfandStarTransform A ((gelfandStarTransform A).symm F) χ = _
  rw [StarAlgEquiv.apply_symm_apply]

theorem projections_separate_characters [WStarAlgebra A]
    (χ ψ : characterSpace ℂ A) (hne : χ ≠ ψ) :
    ∃ p : ProjAlg A, gelfandTransform ℂ A p.val χ = 1 ∧ gelfandTransform ℂ A p.val ψ = 0 := by
  obtain ⟨k, hk0, hk1, hk⟩ := exists_continuous_zero_one_of_isClosed
    (isClosed_singleton : IsClosed ({ψ} : Set (characterSpace ℂ A)))
    (isClosed_singleton : IsClosed ({χ} : Set (characterSpace ℂ A)))
    (show Disjoint ({ψ} : Set (characterSpace ℂ A)) {χ} by simp [hne.symm])
  have hkψ : k ψ = 0 := hk0 (Set.mem_singleton ψ)
  have hkχ : k χ = 1 := hk1 (Set.mem_singleton χ)
  let f : C(characterSpace ℂ A, ℝ) := ⟨fun x => k x - 1 / 2, by fun_prop⟩
  let F : C(characterSpace ℂ A, ℂ) := ⟨fun x => (min (2 * k x) 1 : ℝ), by fun_prop⟩
  let b : A := (gelfandStarTransform A).symm F
  have hb : PositiveUnit b := by
    intro x
    rw [inverse_eval]
    exact ⟨rfl, le_min (mul_nonneg (by norm_num) (hk x).1) zero_le_one, min_le_right _ _⟩
  obtain ⟨p, hpone, hpup, hleast⟩ := exists_support_projection f
  have hpb : SpectralLE p.val b := by
    apply hleast b hb
    intro n x
    rw [ramp_eval, inverse_eval]
    change min ((n : ℝ) * max (k x - 1 / 2) 0) 1 ≤ min (2 * k x) 1
    by_cases hx : k x ≤ 1 / 2
    · rw [max_eq_right (by linarith), mul_zero, min_eq_left zero_le_one]
      exact le_min (mul_nonneg (by norm_num) (hk x).1) zero_le_one
    · rw [min_eq_right (show 1 ≤ 2 * k x by linarith)]
      exact min_le_right _ _
  have hpψ : gelfandTransform ℂ A p.val ψ = 0 := by
    have hle := hpb ψ
    rw [inverse_eval] at hle
    change (gelfandTransform ℂ A p.val ψ).re ≤ min (2 * k ψ) 1 at hle
    rw [hkψ, mul_zero, min_eq_left zero_le_one] at hle
    apply Complex.ext
    · exact le_antisymm hle (projection_positiveUnit p ψ).2.1
    · exact (projection_positiveUnit p ψ).1
  refine ⟨p, hpone χ ?_, hpψ⟩
  change 0 < k χ - 1 / 2
  rw [hkχ]
  norm_num

def projectionMonoid (A : Type*) [CommCStarAlgebra A] : Submonoid A where
  carrier := Set.range (ProjAlg.val : ProjAlg A → A)
  one_mem' := ⟨⊤, rfl⟩
  mul_mem' := by
    rintro a b ⟨p, rfl⟩ ⟨q, rfl⟩
    exact ⟨p ⊓ q, rfl⟩

lemma projection_adjoin_span (A : Type*) [CommCStarAlgebra A] :
    (StarAlgebra.adjoin ℂ (Set.range (ProjAlg.val : ProjAlg A → A))).toSubalgebra.toSubmodule =
      Submodule.span ℂ (Set.range (ProjAlg.val : ProjAlg A → A)) := by
  have hs : star (Set.range (ProjAlg.val : ProjAlg A → A)) =
      Set.range (ProjAlg.val : ProjAlg A → A) := by
    rw [← Set.image_star]
    ext a
    constructor
    · rintro ⟨b, ⟨p, rfl⟩, rfl⟩
      exact ⟨p, p.isStarProjection.2.symm⟩
    · rintro ⟨p, rfl⟩
      exact ⟨p.val, ⟨p, rfl⟩, p.isStarProjection.2⟩
  rw [StarAlgebra.adjoin_eq_span, hs, Set.union_self]
  change Submodule.span ℂ (Submonoid.closure (projectionMonoid A : Set A) : Set A) = _
  rw [Submonoid.closure_eq]
  rfl

theorem projection_span_dense (A : Type*) [CommCStarAlgebra A] [WStarAlgebra A] :
    Dense (Submodule.span ℂ (Set.range (ProjAlg.val : ProjAlg A → A)) : Set A) := by
  let S : StarSubalgebra ℂ A := StarAlgebra.adjoin ℂ (Set.range (ProjAlg.val : ProjAlg A → A))
  let g : A →⋆ₐ[ℂ] C(characterSpace ℂ A, ℂ) := (gelfandStarTransform A).toStarAlgHom
  have hsep : (S.map g).SeparatesPoints := by
    intro χ ψ hne
    obtain ⟨p, hpχ, hpψ⟩ := projections_separate_characters χ ψ hne
    refine ⟨fun x => g p.val x, ⟨g p.val, ?_, rfl⟩, ?_⟩
    · exact StarSubalgebra.mem_map.mpr
        ⟨p.val, StarAlgebra.subset_adjoin ℂ _ ⟨p, rfl⟩, rfl⟩
    · change gelfandTransform ℂ A p.val χ ≠ gelfandTransform ℂ A p.val ψ
      rw [hpχ, hpψ]
      exact one_ne_zero
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    (S.map g) hsep
  have hdense : Dense (S : Set A) := by
    apply (gelfandTransform_isometry A).isEmbedding.isInducing.dense_iff.mpr
    intro a
    change g a ∈ (S.map g).topologicalClosure
    rw [htop]
    trivial
  rw [← projection_adjoin_span A]
  exact hdense


end Gelfand39Inverse


set_option autoImplicit false

namespace Gelfand39Inverse

open scoped BigOperators

noncomputable section

variable {B : Type*} [BooleanAlgebra B]

def binaryPartition (p : B) : Finpartition (⊤ : B) := by
  classical
  apply Finpartition.ofErase {p, pᶜ}
  · rw [Finset.supIndep_iff_pairwiseDisjoint]
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (hab rfl).elim
    · exact disjoint_compl_right
    · exact disjoint_compl_left
    · exact (hab rfl).elim
  · simp

lemma binaryPartition_decides (p q : B) (hq : q ∈ (binaryPartition p).parts) :
    q ≤ p ∨ q ≤ pᶜ := by
  classical
  have h : q ∈ ({p, pᶜ} : Finset B) := Finset.mem_of_mem_erase hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl
  · exact Or.inl le_rfl
  · exact Or.inr le_rfl

theorem exists_deciding_partition (s : Finset B) :
    ∃ P : Finpartition (⊤ : B), ∀ q ∈ P.parts, ∀ p ∈ s, q ≤ p ∨ q ≤ pᶜ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨⊤, by simp⟩
  | @insert p s hp ih =>
    obtain ⟨P, hP⟩ := ih
    refine ⟨P ⊓ binaryPartition p, ?_⟩
    intro q hq r hr
    rcases Finset.mem_insert.mp hr with hr | hr
    · rw [hr]
      obtain ⟨b, hb, hqb⟩ := (inf_le_right : P ⊓ binaryPartition p ≤ binaryPartition p) hq
      exact (binaryPartition_decides p b hb).imp (hqb.trans) (hqb.trans)
    · obtain ⟨b, hb, hqb⟩ := (inf_le_left : P ⊓ binaryPartition p ≤ P) hq
      exact (hP b hb r hr).imp (hqb.trans) (hqb.trans)

variable {M : Type*} [AddCommMonoid M] (ν : B → M)
    (hzero : ν ⊥ = 0) (hadd : ∀ p q, Disjoint p q → ν (p ⊔ q) = ν p + ν q)

include hzero hadd

lemma valuation_sup_sum (s : Finset B) (hs : (s : Set B).PairwiseDisjoint id) :
    ν (s.sup id) = ∑ p ∈ s, ν p := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hzero
  | @insert p s hp ih =>
    have hps : Disjoint p (s.sup id) := by
      rw [Finset.disjoint_sup_right]
      intro q hq
      exact hs (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hq) (by
        intro he; exact hp (he ▸ hq))
    rw [Finset.sup_insert, id_eq, hadd p (s.sup id) hps, Finset.sum_insert hp]
    rw [ih (fun a ha b hb hab => hs (Finset.mem_insert_of_mem ha)
      (Finset.mem_insert_of_mem hb) hab)]

lemma valuation_partition_sum {a : B} (P : Finpartition a) :
    ∑ q ∈ P.parts, ν q = ν a := by
  rw [← valuation_sup_sum ν hzero hadd P.parts P.disjoint, P.sup_parts]

lemma valuation_partition_inf_sum (P : Finpartition (⊤ : B)) (p : B) :
    ∑ q ∈ P.parts, ν (q ⊓ p) = ν p := by
  classical
  rw [← P.sum_restrict le_top ν hzero]
  exact valuation_partition_sum ν hzero hadd (P.restrict le_top)

end
end Gelfand39Inverse


set_option autoImplicit false

namespace Gelfand39Inverse

open Gelfand38 GelfandVNA.Duality WeakDual
open scoped BigOperators

noncomputable section

variable {A : Type*} [CommCStarAlgebra A]

lemma exists_character_projection_one (p : ProjAlg A) (hp : p ≠ ⊥) :
    ∃ χ : characterSpace ℂ A, gelfandTransform ℂ A p.val χ = 1 := by
  by_contra! hn
  have hz : gelfandTransform ℂ A p.val = 0 := by
    ext χ
    rcases projection_value_zero_or_one p χ with h | h
    · exact h
    · exact (hn χ h).elim
  have hpz : p.val = 0 := (gelfandTransform_isometry A).injective (by simpa using hz)
  apply hp
  apply Subtype.ext
  apply Subtype.ext
  exact hpz

lemma character_norm_le (χ : characterSpace ℂ A) (a : A) :
    ‖gelfandTransform ℂ A a χ‖ ≤ ‖a‖ := by
  simpa only [gelfand_norm] using ContinuousMap.norm_coe_le_norm (gelfandTransform ℂ A a) χ

def partitionFunctional (ν : ProjAlg A → ℝ) (P : Finpartition (⊤ : ProjAlg A)) : A →L[ℂ] ℂ :=
  ∑ q : P.parts, (ν q.val : ℂ) • CharacterSpace.toCLM
    (Classical.choose (exists_character_projection_one q.val (P.ne_bot q.property)))

lemma partitionFunctional_apply (ν : ProjAlg A → ℝ) (P : Finpartition (⊤ : ProjAlg A)) (a : A) :
    partitionFunctional ν P a = ∑ q : P.parts, (ν q.val : ℂ) *
      gelfandTransform ℂ A a
        (Classical.choose (exists_character_projection_one q.val (P.ne_bot q.property))) := by
  simp only [partitionFunctional, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  rfl

variable (ν : ProjAlg A → ℝ) (hzero : ν ⊥ = 0)
    (hadd : ∀ p q, Disjoint p q → ν (p ⊔ q) = ν p + ν q)

include hzero hadd

lemma partitionFunctional_norm_le (hpos : ∀ p, 0 ≤ ν p)
    (P : Finpartition (⊤ : ProjAlg A)) (a : A) :
    ‖partitionFunctional ν P a‖ ≤ ν ⊤ * ‖a‖ := by
  classical
  rw [partitionFunctional_apply]
  calc
    _ ≤ ∑ q : P.parts, ‖(ν q.val : ℂ) * gelfandTransform ℂ A a
        (Classical.choose (exists_character_projection_one q.val (P.ne_bot q.property)))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ q : P.parts, ν q.val * ‖a‖ := by
      apply Finset.sum_le_sum
      intro q hq
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpos q.val)]
      exact mul_le_mul_of_nonneg_left (character_norm_le _ a) (hpos q.val)
    _ = ν ⊤ * ‖a‖ := by
      rw [← Finset.sum_mul]
      congr 1
      simpa only [Finset.sum_coe_sort] using valuation_partition_sum ν hzero hadd P

lemma partitionFunctional_projection (P : Finpartition (⊤ : ProjAlg A)) (p : ProjAlg A)
    (hdec : ∀ q ∈ P.parts, q ≤ p ∨ q ≤ pᶜ) :
    partitionFunctional ν P p.val = (ν p : ℂ) := by
  classical
  rw [partitionFunctional_apply]
  calc
    _ = ∑ q : P.parts, (ν (q.val ⊓ p) : ℂ) := by
      apply Finset.sum_congr rfl
      intro q hq
      let χ := Classical.choose (exists_character_projection_one q.val (P.ne_bot q.property))
      have hχ : gelfandTransform ℂ A q.val.val χ = 1 :=
        Classical.choose_spec (exists_character_projection_one q.val (P.ne_bot q.property))
      change (ν q.val : ℂ) * gelfandTransform ℂ A p.val χ = _
      rcases hdec q.val q.property with hqp | hqp
      · have he := congrArg (fun r : ProjAlg A => gelfandTransform ℂ A r.val χ)
          (inf_eq_left.mpr hqp)
        change gelfandTransform ℂ A (q.val.val * p.val) χ = _ at he
        simp only [map_mul, ContinuousMap.mul_apply, hχ, one_mul] at he
        rw [he, mul_one, inf_eq_left.mpr hqp]
      · have hdis : Disjoint q.val p := le_compl_iff_disjoint_right.mp hqp
        have he := congrArg (fun r : ProjAlg A => gelfandTransform ℂ A r.val χ) hdis.eq_bot
        change gelfandTransform ℂ A (q.val.val * p.val) χ = gelfandTransform ℂ A 0 χ at he
        simp only [map_mul, ContinuousMap.mul_apply, hχ, one_mul, map_zero,
          ContinuousMap.zero_apply] at he
        rw [he, mul_zero, hdis.eq_bot, hzero, Complex.ofReal_zero]
    _ = (ν p : ℂ) := by
      rw [← Complex.ofReal_sum]
      congr 1
      exact (Finset.sum_coe_sort P.parts (fun q => ν (q ⊓ p))).trans
        (valuation_partition_inf_sum ν hzero hadd P p)


end
end Gelfand39Inverse


set_option autoImplicit false

namespace Gelfand39Inverse

open GelfandVNA.Duality

noncomputable section

variable {A : Type*} [CommCStarAlgebra A]

lemma projection_linearCombination_bound (ν : ProjAlg A → ℝ) (hzero : ν ⊥ = 0)
    (hadd : ∀ p q, Disjoint p q → ν (p ⊔ q) = ν p + ν q) (hpos : ∀ p, 0 ≤ ν p)
    (c : ProjAlg A →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ (fun p => (ν p : ℂ)) c‖ ≤
      ν ⊤ * ‖Finsupp.linearCombination ℂ (ProjAlg.val : ProjAlg A → A) c‖ := by
  obtain ⟨P, hP⟩ := exists_deciding_partition c.support
  have he : partitionFunctional ν P
      (Finsupp.linearCombination ℂ (ProjAlg.val : ProjAlg A → A) c) =
      Finsupp.linearCombination ℂ (fun p => (ν p : ℂ)) c := by
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro p hp
    rw [partitionFunctional_projection ν hzero hadd P p (fun q hq => hP q hq p hp)]
  rw [← he]
  exact partitionFunctional_norm_le ν hzero hadd hpos P _

lemma projection_linearCombination_dense [WStarAlgebra A] :
    DenseRange (Finsupp.linearCombination ℂ (ProjAlg.val : ProjAlg A → A)) := by
  change Dense (LinearMap.range (Finsupp.linearCombination ℂ (ProjAlg.val : ProjAlg A → A)) : Set A)
  rw [Finsupp.range_linearCombination]
  exact projection_span_dense A

theorem positive_valuation_bounded_extension [WStarAlgebra A]
    (ν : ProjAlg A → ℝ) (hzero : ν ⊥ = 0)
    (hadd : ∀ p q, Disjoint p q → ν (p ⊔ q) = ν p + ν q) (hpos : ∀ p, 0 ≤ ν p) :
    ∃! φ : A →L[ℂ] ℂ, ∀ p : ProjAlg A, φ p.val = (ν p : ℂ) := by
  let f := Finsupp.linearCombination ℂ (fun p : ProjAlg A => (ν p : ℂ))
  let e := Finsupp.linearCombination ℂ (ProjAlg.val : ProjAlg A → A)
  have hd : DenseRange e := projection_linearCombination_dense
  have hb : ∃ C : ℝ, ∀ c, ‖f c‖ ≤ C * ‖e c‖ :=
    ⟨ν ⊤, projection_linearCombination_bound ν hzero hadd hpos⟩
  refine ⟨f.extendOfNorm e, ?_, ?_⟩
  · intro p
    have h := LinearMap.extendOfNorm_eq hd hb (Finsupp.single p (1 : ℂ))
    simpa only [f, e, Finsupp.linearCombination_single, one_smul] using h
  · intro φ hφ
    apply ContinuousLinearMap.ext_on (projection_span_dense A)
    rintro a ⟨p, rfl⟩
    rw [hφ p]
    have h := LinearMap.extendOfNorm_eq hd hb (Finsupp.single p (1 : ℂ))
    simpa only [f, e, Finsupp.linearCombination_single, one_smul] using h.symm


end
end Gelfand39Inverse


set_option autoImplicit false

namespace Gelfand39Inverse

open GelfandVNA.Duality QAlgorithms.Papers.Independent.Support21.P20

noncomputable section

variable {A : Type*} [CommCStarAlgebra A]

theorem normal_functional_existsCLM (φ : A → ℂ) (hφ : IsNormalFunctional φ) :
    ∃ Φ : A →L[ℂ] ℂ, ∀ a, Φ a = φ a := by
  obtain ⟨X, hX, hN, hC, e, x, hφ⟩ := hφ
  have heq : φ = fun a => star ((e.symm a) x) := funext hφ
  refine ⟨{ toFun := φ
            map_add' := ?_
            map_smul' := ?_
            cont := ?_ }, fun _ => rfl⟩
  · intro a b
    simp [hφ]
  · intro c a
    rw [hφ, hφ, e.symm.map_smulₛₗ]
    simp
  · rw [heq]
    fun_prop

theorem normal_functionals_ext_projections [WStarAlgebra A]
    (φ ψ : A → ℂ) (hφ : IsNormalFunctional φ) (hψ : IsNormalFunctional ψ)
    (h : ∀ p : ProjAlg A, φ p.val = ψ p.val) : φ = ψ := by
  obtain ⟨Φ, hΦ⟩ := normal_functional_existsCLM φ hφ
  obtain ⟨Ψ, hΨ⟩ := normal_functional_existsCLM ψ hψ
  have he : Φ = Ψ := by
    apply ContinuousLinearMap.ext_on (projection_span_dense A)
    rintro a ⟨p, rfl⟩
    rw [hΦ, hΨ, h p]
  funext a
  rw [← hΦ a, ← hΨ a, he]

theorem positive_continuous_valuation_bounded_extension [WStarAlgebra A]
    (ν : ProjAlg A → NNReal) (hν : IsPositiveContinuousValuation ν) :
    ∃! Φ : A →L[ℂ] ℂ, ∀ p : ProjAlg A, Φ p.val = (ν p : ℂ) := by
  apply positive_valuation_bounded_extension (fun p => (ν p : ℝ))
  · exact_mod_cast hν.1.1
  · intro p q hd
    have h := hν.1.2 p q
    rw [hd.eq_bot, hν.1.1, add_zero] at h
    exact_mod_cast h.symm
  · intro p
    exact (ν p).coe_nonneg


end
end Gelfand39Inverse
end Gelfand320WholeSource3

/- Source module Work.Gelfand320.StepDensity; SHA256 c2c0b9dff0a176c30c2479c2de9891b1b75066e72390e938a66ed1622099cf4d. -/
section Gelfand320WholeSource4

set_option autoImplicit false
namespace Gelfand320
open Set TopologicalSpace GelfandVNA.Duality
noncomputable section
universe u

/-- The Boolean prime spectrum has a basis of clopen sets and hence is totally separated. -/
theorem booleanSpectrum_totallySeparated (B : Type u) [BooleanAlgebra B] :
    TotallySeparatedSpace (PrimeSpectrum (AsBoolRing B)) := by
  apply totallySeparatedSpace_of_t0_of_basis_clopen
  apply isTopologicalBasis_of_isOpen_of_nhds (fun _ hs => hs.isOpen)
  intro x U hx hU
  let O : Opens (PrimeSpectrum (AsBoolRing B)) := ⟨U, hU⟩
  have hx' : x ∈ sSup (Gelfand272Spectrum.basis B ''
      {b | Gelfand272Spectrum.basis B b ≤ O}) := by
    rw [← Gelfand272Spectrum.basis_density B O]
    exact hx
  obtain ⟨V, ⟨b, hb, rfl⟩, hxb⟩ := Opens.mem_sSup.mp hx'
  exact ⟨Gelfand272Spectrum.clopensIso B b,
    (Gelfand272Spectrum.clopensIso B b).isClopen, hxb, hb⟩

/-- On a compact totally separated space, continuous functions are norm limits
of linear combinations of characteristic functions of clopens. -/
theorem continuous_projection_span_dense (K : Type u) [TopologicalSpace K]
    [CompactSpace K] [TotallySeparatedSpace K] :
    Dense (Submodule.span ℂ (Set.range (ProjAlg.val : ProjAlg C(K, ℂ) → C(K, ℂ))) : Set C(K, ℂ)) := by
  let S : StarSubalgebra ℂ C(K, ℂ) :=
    StarAlgebra.adjoin ℂ (Set.range (ProjAlg.val : ProjAlg C(K, ℂ) → C(K, ℂ)))
  have hsep : S.SeparatesPoints := by
    intro x y hxy
    obtain ⟨U, hU, hx, hy⟩ := exists_isClopen_of_totally_separated hxy
    let V : Clopens K := ⟨U, hU⟩
    refine ⟨fun x => clopenIndicator V x, ⟨clopenIndicator V, ?_, rfl⟩, ?_⟩
    · exact StarAlgebra.subset_adjoin ℂ _ ⟨clopenProjection V, rfl⟩
    · have hy' : y ∉ U := hy
      simp [clopenIndicator, V, hx, hy']
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints S hsep
  have hdense : Dense (S : Set C(K, ℂ)) := by
    rw [dense_iff_closure_eq]
    change (S.topologicalClosure : Set C(K, ℂ)) = Set.univ
    rw [htop]
    rfl
  rw [← Gelfand39Inverse.projection_adjoin_span C(K, ℂ)]
  exact hdense

theorem boolean_step_projection_span_dense (B : Type u) [BooleanAlgebra B] :
    Dense (Submodule.span ℂ (Set.range (ProjAlg.val :
      ProjAlg C(PrimeSpectrum (AsBoolRing B), ℂ) → C(PrimeSpectrum (AsBoolRing B), ℂ))) :
      Set C(PrimeSpectrum (AsBoolRing B), ℂ)) := by
  letI := booleanSpectrum_totallySeparated B
  exact continuous_projection_span_dense _

end
end Gelfand320
end Gelfand320WholeSource4

/- Source module Work.Gelfand39OrderContinuity; SHA256 aaa0af2575525ac15c5498967879f48f4c52914cf2c33da57a89649b2aef5966. -/
section Gelfand320WholeSource5

set_option autoImplicit false

namespace Gelfand39OrderContinuity

open GelfandVNA.Duality Gelfand38 Gelfand39Inverse WeakDual
open scoped BigOperators ComplexOrder

noncomputable section

variable {A : Type*} [CommCStarAlgebra A]

section OrderBridge

variable [PartialOrder A] [StarOrderedRing A]

lemma gelfand_le_iff (a b : A) :
    (∀ χ : characterSpace ℂ A, gelfandTransform ℂ A a χ ≤ gelfandTransform ℂ A b χ) ↔ a ≤ b := by
  constructor
  · intro h
    have h' : gelfandStarTransform A a ≤ gelfandStarTransform A b := h
    simpa only [StarAlgEquiv.symm_apply_apply] using
      OrderHomClass.mono (gelfandStarTransform A).symm h'
  · intro h
    exact OrderHomClass.mono (gelfandStarTransform A) h

lemma spectralLE_iff_le {a b : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    SpectralLE a b ↔ a ≤ b := by
  rw [← gelfand_le_iff]
  constructor
  · intro h χ
    exact Complex.le_def.mpr ⟨h χ, by
      rw [(gelfand_selfAdjoint_iff a).mp ha χ, (gelfand_selfAdjoint_iff b).mp hb χ]⟩
  · intro h χ
    exact (Complex.le_def.mp (h χ)).1

lemma positiveUnit_iff_mem_Icc (a : A) : PositiveUnit a ↔ a ∈ Set.Icc (0 : A) 1 := by
  rw [Set.mem_Icc, ← gelfand_le_iff, ← gelfand_le_iff]
  simp only [map_zero, ContinuousMap.zero_apply, map_one, ContinuousMap.one_apply]
  constructor
  · intro h
    exact ⟨fun χ => Complex.nonneg_iff.mpr ⟨(h χ).2.1, (h χ).1.symm⟩,
      fun χ => Complex.le_def.mpr ⟨(h χ).2.2, (h χ).1⟩⟩
  · rintro ⟨h0, h1⟩ χ
    exact ⟨(Complex.nonneg_iff.mp (h0 χ)).2.symm,
      (Complex.nonneg_iff.mp (h0 χ)).1, (Complex.le_def.mp (h1 χ)).1⟩

lemma partitionFunctional_nonneg (ν : ProjAlg A → ℝ) (hpos : ∀ p, 0 ≤ ν p)
    (P : Finpartition (⊤ : ProjAlg A)) {a : A} (ha : 0 ≤ a) :
    0 ≤ partitionFunctional ν P a := by
  classical
  rw [partitionFunctional_apply]
  apply Finset.sum_nonneg
  intro q hq
  apply mul_nonneg
  · exact Complex.nonneg_iff.mpr ⟨hpos q.val, rfl⟩
  · have hg : 0 ≤ gelfandStarTransform A a := map_nonneg (gelfandStarTransform A) ha
    exact hg _

end OrderBridge

variable [WStarAlgebra A]

lemma extension_norm_bound (ν : ProjAlg A → ℝ) (hzero : ν ⊥ = 0)
    (hadd : ∀ p q, Disjoint p q → ν (p ⊔ q) = ν p + ν q) (hpos : ∀ p, 0 ≤ ν p)
    (Φ : A →L[ℂ] ℂ) (hΦ : ∀ p : ProjAlg A, Φ p.val = (ν p : ℂ)) (a : A) :
    ‖Φ a‖ ≤ ν ⊤ * ‖a‖ := by
  refine (projection_linearCombination_dense (A := A)).induction_on
    (p := fun a => ‖Φ a‖ ≤ ν ⊤ * ‖a‖) a
    (isClosed_le (by fun_prop) (by fun_prop)) ?_
  intro c
  have he : Φ (Finsupp.linearCombination ℂ (ProjAlg.val : ProjAlg A → A) c) =
      Finsupp.linearCombination ℂ (fun p => (ν p : ℂ)) c := by
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul, hΦ]
  rw [he]
  exact projection_linearCombination_bound ν hzero hadd hpos c

lemma extension_opNorm_bound (ν : ProjAlg A → ℝ) (hzero : ν ⊥ = 0)
    (hadd : ∀ p q, Disjoint p q → ν (p ⊔ q) = ν p + ν q) (hpos : ∀ p, 0 ≤ ν p)
    (Φ : A →L[ℂ] ℂ) (hΦ : ∀ p : ProjAlg A, Φ p.val = (ν p : ℂ)) :
    ‖Φ‖ ≤ ν ⊤ :=
  Φ.opNorm_le_bound (hpos ⊤) (extension_norm_bound ν hzero hadd hpos Φ hΦ)

lemma extension_nonneg [PartialOrder A] [StarOrderedRing A]
    (ν : ProjAlg A → ℝ) (hzero : ν ⊥ = 0)
    (hadd : ∀ p q, Disjoint p q → ν (p ⊔ q) = ν p + ν q) (hpos : ∀ p, 0 ≤ ν p)
    (Φ : A →L[ℂ] ℂ) (hΦ : ∀ p : ProjAlg A, Φ p.val = (ν p : ℂ))
    {a : A} (ha : 0 ≤ a) : 0 ≤ Φ a := by
  classical
  have hcl : Φ a ∈ closure {z : ℂ | 0 ≤ z} := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let K : ℝ := ‖Φ‖ + ν ⊤ + 1
    have hK : 0 < K := by dsimp [K]; linarith [norm_nonneg Φ, hpos ⊤]
    obtain ⟨c, hc⟩ := (projection_linearCombination_dense (A := A)).exists_dist_lt a
      (div_pos hε hK)
    let b := Finsupp.linearCombination ℂ (ProjAlg.val : ProjAlg A → A) c
    obtain ⟨P, hP⟩ := exists_deciding_partition c.support
    let F := partitionFunctional ν P
    have he : Φ b = F b := by
      dsimp [b]
      simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [hΦ, partitionFunctional_projection ν hzero hadd P p (fun q hq => hP q hq p hp)]
    refine ⟨F a, partitionFunctional_nonneg ν hpos P ha, ?_⟩
    rw [dist_eq_norm]
    have heq : Φ a - F a = Φ (a - b) - F (a - b) := by
      rw [map_sub, map_sub, he]
      abel
    rw [heq]
    calc
      _ ≤ ‖Φ (a - b)‖ + ‖F (a - b)‖ := norm_sub_le _ _
      _ ≤ ‖Φ‖ * ‖a - b‖ + ν ⊤ * ‖a - b‖ :=
        add_le_add (Φ.le_opNorm _) (partitionFunctional_norm_le ν hzero hadd hpos P _)
      _ ≤ K * ‖a - b‖ := by
        rw [← add_mul]
        exact mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) (norm_nonneg _)
      _ < ε := by
        have hc' : ‖a - b‖ < ε / K := by simpa only [dist_eq_norm] using hc
        exact (lt_div_iff₀' hK).mp hc'
  rw [(show IsClosed {z : ℂ | 0 ≤ z} from isClosed_Ici).closure_eq] at hcl
  exact hcl

def extensionPositiveLinearMap [PartialOrder A] [StarOrderedRing A]
    (ν : ProjAlg A → ℝ) (hzero : ν ⊥ = 0)
    (hadd : ∀ p q, Disjoint p q → ν (p ⊔ q) = ν p + ν q) (hpos : ∀ p, 0 ≤ ν p)
    (Φ : A →L[ℂ] ℂ) (hΦ : ∀ p : ProjAlg A, Φ p.val = (ν p : ℂ)) : A →ₚ[ℂ] ℂ where
  toLinearMap := Φ.toLinearMap
  monotone' := by
    intro a b hab
    change Φ a ≤ Φ b
    have h := extension_nonneg ν hzero hadd hpos Φ hΦ (sub_nonneg.mpr hab)
    simpa only [map_sub, sub_nonneg] using h


end
end Gelfand39OrderContinuity
end Gelfand320WholeSource5

/- Source module Work.Gelfand320.StepPositiveExtension; SHA256 732de2cbec08bd6380988a8c2cfe1b87ed5d7b1eb95516f84f3ea777ec7f4cc6. -/
section Gelfand320WholeSource6

set_option autoImplicit false
namespace Gelfand320.Step
open GelfandVNA.Duality Gelfand38 Gelfand39Inverse Gelfand39OrderContinuity WeakDual
open scoped BigOperators ComplexOrder
noncomputable section
variable {A : Type*} [CommCStarAlgebra A]
variable (hDense : Dense (Submodule.span ℂ (Set.range (ProjAlg.val : ProjAlg A → A)) : Set A))
include hDense

lemma linearCombination_dense :
    DenseRange (Finsupp.linearCombination ℂ (ProjAlg.val : ProjAlg A → A)) := by
  change Dense (LinearMap.range (Finsupp.linearCombination ℂ (ProjAlg.val : ProjAlg A → A)) : Set A)
  rw [Finsupp.range_linearCombination]
  exact hDense

/- The following arguments are the checked3.9 bounded extension proofs with the
sole density input supplied explicitly. They require no WStarAlgebra instance. -/
theorem positive_valuation_bounded_extension
    (ν : ProjAlg A → ℝ) (hzero : ν ⊥ = 0)
    (hadd : ∀ p q, Disjoint p q → ν (p ⊔ q) = ν p + ν q) (hpos : ∀ p, 0 ≤ ν p) :
    ∃! φ : A →L[ℂ] ℂ, ∀ p : ProjAlg A, φ p.val = (ν p : ℂ) := by
  let f := Finsupp.linearCombination ℂ (fun p : ProjAlg A => (ν p : ℂ))
  let e := Finsupp.linearCombination ℂ (ProjAlg.val : ProjAlg A → A)
  have hd : DenseRange e := linearCombination_dense hDense
  have hb : ∃ C : ℝ, ∀ c, ‖f c‖ ≤ C * ‖e c‖ :=
    ⟨ν ⊤, projection_linearCombination_bound ν hzero hadd hpos⟩
  refine ⟨f.extendOfNorm e, ?_, ?_⟩
  · intro p
    have h := LinearMap.extendOfNorm_eq hd hb (Finsupp.single p (1 : ℂ))
    simpa only [f, e, Finsupp.linearCombination_single, one_smul] using h
  · intro φ hφ
    apply ContinuousLinearMap.ext_on hDense
    rintro a ⟨p, rfl⟩
    rw [hφ p]
    have h := LinearMap.extendOfNorm_eq hd hb (Finsupp.single p (1 : ℂ))
    simpa only [f, e, Finsupp.linearCombination_single, one_smul] using h.symm

lemma extension_norm_bound (ν : ProjAlg A → ℝ) (hzero : ν ⊥ = 0)
    (hadd : ∀ p q, Disjoint p q → ν (p ⊔ q) = ν p + ν q) (hpos : ∀ p, 0 ≤ ν p)
    (Φ : A →L[ℂ] ℂ) (hΦ : ∀ p : ProjAlg A, Φ p.val = (ν p : ℂ)) (a : A) :
    ‖Φ a‖ ≤ ν ⊤ * ‖a‖ := by
  refine (linearCombination_dense hDense).induction_on
    (p := fun a => ‖Φ a‖ ≤ ν ⊤ * ‖a‖) a
    (isClosed_le (by fun_prop) (by fun_prop)) ?_
  intro c
  have he : Φ (Finsupp.linearCombination ℂ (ProjAlg.val : ProjAlg A → A) c) =
      Finsupp.linearCombination ℂ (fun p => (ν p : ℂ)) c := by
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul, hΦ]
  rw [he]
  exact projection_linearCombination_bound ν hzero hadd hpos c

lemma extension_opNorm_bound (ν : ProjAlg A → ℝ) (hzero : ν ⊥ = 0)
    (hadd : ∀ p q, Disjoint p q → ν (p ⊔ q) = ν p + ν q) (hpos : ∀ p, 0 ≤ ν p)
    (Φ : A →L[ℂ] ℂ) (hΦ : ∀ p : ProjAlg A, Φ p.val = (ν p : ℂ)) :
    ‖Φ‖ ≤ ν ⊤ :=
  Φ.opNorm_le_bound (hpos ⊤) (extension_norm_bound hDense ν hzero hadd hpos Φ hΦ)

lemma extension_nonneg [PartialOrder A] [StarOrderedRing A]
    (ν : ProjAlg A → ℝ) (hzero : ν ⊥ = 0)
    (hadd : ∀ p q, Disjoint p q → ν (p ⊔ q) = ν p + ν q) (hpos : ∀ p, 0 ≤ ν p)
    (Φ : A →L[ℂ] ℂ) (hΦ : ∀ p : ProjAlg A, Φ p.val = (ν p : ℂ))
    {a : A} (ha : 0 ≤ a) : 0 ≤ Φ a := by
  classical
  have hcl : Φ a ∈ closure {z : ℂ | 0 ≤ z} := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let K : ℝ := ‖Φ‖ + ν ⊤ + 1
    have hK : 0 < K := by dsimp [K]; linarith [norm_nonneg Φ, hpos ⊤]
    obtain ⟨c, hc⟩ := (linearCombination_dense hDense).exists_dist_lt a
      (div_pos hε hK)
    let b := Finsupp.linearCombination ℂ (ProjAlg.val : ProjAlg A → A) c
    obtain ⟨P, hP⟩ := exists_deciding_partition c.support
    let F := partitionFunctional ν P
    have he : Φ b = F b := by
      dsimp [b]
      simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [hΦ, partitionFunctional_projection ν hzero hadd P p (fun q hq => hP q hq p hp)]
    refine ⟨F a, partitionFunctional_nonneg ν hpos P ha, ?_⟩
    rw [dist_eq_norm]
    have heq : Φ a - F a = Φ (a - b) - F (a - b) := by
      rw [map_sub, map_sub, he]
      abel
    rw [heq]
    calc
      _ ≤ ‖Φ (a - b)‖ + ‖F (a - b)‖ := norm_sub_le _ _
      _ ≤ ‖Φ‖ * ‖a - b‖ + ν ⊤ * ‖a - b‖ :=
        add_le_add (Φ.le_opNorm _) (partitionFunctional_norm_le ν hzero hadd hpos P _)
      _ ≤ K * ‖a - b‖ := by
        rw [← add_mul]
        exact mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) (norm_nonneg _)
      _ < ε := by
        have hc' : ‖a - b‖ < ε / K := by simpa only [dist_eq_norm] using hc
        exact (lt_div_iff₀' hK).mp hc'
  rw [(show IsClosed {z : ℂ | 0 ≤ z} from isClosed_Ici).closure_eq] at hcl
  exact hcl

def extensionPositiveLinearMap [PartialOrder A] [StarOrderedRing A]
    (ν : ProjAlg A → ℝ) (hzero : ν ⊥ = 0)
    (hadd : ∀ p q, Disjoint p q → ν (p ⊔ q) = ν p + ν q) (hpos : ∀ p, 0 ≤ ν p)
    (Φ : A →L[ℂ] ℂ) (hΦ : ∀ p : ProjAlg A, Φ p.val = (ν p : ℂ)) : A →ₚ[ℂ] ℂ where
  toLinearMap := Φ.toLinearMap
  monotone' := by
    intro a b hab
    change Φ a ≤ Φ b
    have h := extension_nonneg hDense ν hzero hadd hpos Φ hΦ (sub_nonneg.mpr hab)
    simpa only [map_sub, sub_nonneg] using h


end
end Gelfand320.Step
end Gelfand320WholeSource6

/- Source module Work.Gelfand39ValuationSup; SHA256 de19a3a4ede458eb9d6a911c67ff01fcda84ad0e196a2921ca72926595378c78. -/
section Gelfand320WholeSource7

set_option autoImplicit false
noncomputable section
open Set Filter QAlgorithms.Papers.Independent.Support21.P20

namespace Gelfand39ValuationSup
universe u
variable {B : Type u} [CompleteBooleanAlgebra B]

theorem disjoint_add (ν : B → ℝ) (hν : IsValuation ν)
    (p q : B) (hpq : Disjoint p q) : ν (p ⊔ q) = ν p + ν q := by
  have h := hν.2 p q
  rw [hpq.eq_bot, hν.1] at h
  linarith

theorem monotone_of_positive (ν : B → ℝ) (hν : IsValuation ν)
    (hpos : ∀ p, 0 ≤ ν p) : Monotone ν := by
  intro p q hpq
  have hunion : p ⊔ (q ⊓ pᶜ) = q := by
    rw [sup_inf_left, sup_eq_right.mpr hpq, sup_compl_eq_top, inf_top_eq]
  have hdis : Disjoint p (q ⊓ pᶜ) :=
    (disjoint_compl_right (a := p)).mono_right inf_le_right
  have h := disjoint_add ν hν p (q ⊓ pᶜ) hdis
  rw [hunion] at h
  linarith [hpos (q ⊓ pᶜ)]

/-- Real positive continuous valuations preserve each indicated actual directed
supremum in the order-theoretic sense as well as as a net limit. -/
theorem isLUB_image (ν : B → ℝ) (hν : IsContinuousValuation ν)
    (hpos : ∀ p, 0 ≤ ν p) (s : Set B) (hs : s.Nonempty)
    (hd : DirectedOn (· ≤ ·) s) :
    IsLUB (ν '' s) (ν (sSup s)) := by
  haveI : Nonempty s := hs.to_subtype
  haveI : IsDirected s (· ≤ ·) := ⟨fun a b => by
    obtain ⟨c, hc, hac, hbc⟩ := hd a a.property b b.property
    exact ⟨⟨c, hc⟩, hac, hbc⟩⟩
  have hmono := monotone_of_positive ν hν.1 hpos
  refine ⟨?_, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    exact hmono (le_sSup hb)
  · intro c hc
    exact le_of_tendsto' (hν.2 s (sSup s) hs hd (isLUB_sSup s))
      (fun b => hc ⟨b.val, b.property, rfl⟩)

theorem sub_const_mul_continuous (μ ν : B → ℝ)
    (hμ : IsContinuousValuation μ) (hν : IsContinuousValuation ν) (C : ℝ) :
    IsContinuousValuation (fun p => ν p - C * μ p) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [hμ.1.1, hν.1.1, mul_zero, sub_self]
  · intro p q
    have h₁ := hμ.1.2 p q
    have h₂ := hν.1.2 p q
    linear_combination h₂ - C * h₁
  · intro s a hs hd ha
    exact (hν.2 s a hs hd ha).sub ((hμ.2 s a hs hd ha).const_mul C)

end Gelfand39ValuationSup
end
end Gelfand320WholeSource7

/- Source module Work.Gelfand320.StepPredual; SHA256 b19e0c4ff0d61a1d39d430a4fddeb93ea0e5f7f069ccefbabb385aef347fa155. -/
section Gelfand320WholeSource8

set_option autoImplicit false
namespace Gelfand320
open Set GelfandVNA.Duality QAlgorithms.Papers.Independent.Support21.P20
open scoped ComplexOrder
noncomputable section
universe u
variable (B : Type u) [CompleteBooleanAlgebra B]

abbrev StepAlgebra := C(PrimeSpectrum (AsBoolRing B), ℂ)

local instance : LE (ProjAlg (StepAlgebra B)) :=
  (inferInstance : BooleanAlgebra (ProjAlg (StepAlgebra B))).toPartialOrder.toLE
local instance : Preorder (ProjAlg (StepAlgebra B)) :=
  (inferInstance : BooleanAlgebra (ProjAlg (StepAlgebra B))).toPartialOrder.toPreorder
local instance : PartialOrder (ProjAlg (StepAlgebra B)) :=
  (inferInstance : BooleanAlgebra (ProjAlg (StepAlgebra B))).toPartialOrder

def stepProjection (p : B) : StepAlgebra B := (booleanProjectionIso B p).val

lemma stepProjection_norm (p : B) : ‖stepProjection B p‖ ≤ 1 := by
  exact (booleanProjectionIso B p).isStarProjection.norm_le

/-- The candidate predual consists exactly of bounded functionals whose Boolean
restrictions are continuous valuations. -/
abbrev StepPredual := valuationFunctionals (stepProjection B)

instance stepPredual_normedAddCommGroup : NormedAddCommGroup (StepPredual B) := inferInstance
instance stepPredual_normedSpace : NormedSpace ℂ (StepPredual B) := inferInstance

instance stepPredual_completeSpace : CompleteSpace (StepPredual B) := by
  letI : IsClosed (StepPredual B : Set (StepAlgebra B →L[ℂ] ℂ)) :=
    valuationFunctionals_isClosed (stepProjection B) (stepProjection_norm B)
  infer_instance

/-- Evaluation embeds the step algebra into the dual of its valuation space. -/
def stepEvaluation : StepAlgebra B →L[ℂ] (StepPredual B →L[ℂ] ℂ) :=
  ((ContinuousLinearMap.apply ℂ ℂ : StepAlgebra B →L[ℂ]
    (StepAlgebra B →L[ℂ] ℂ) →L[ℂ] ℂ).flip.comp (StepPredual B).subtypeL).flip

lemma stepEvaluation_apply (a : StepAlgebra B) (φ : StepPredual B) :
    stepEvaluation B a φ = φ.val a := rfl

/-- A positive finite continuous valuation defines an element of the candidate
predual, with the expected sharp upper norm bound. -/
theorem exists_positive_step_functional (ν : B → ℝ)
    (hν : IsContinuousValuation ν) (hpos : ∀ p, 0 ≤ ν p) :
    ∃ φ : StepPredual B, (∀ p, φ.val (stepProjection B p) = (ν p : ℂ)) ∧
      ‖φ‖ ≤ ν ⊤ ∧ ∀ a : StepAlgebra B, 0 ≤ a → 0 ≤ φ.val a := by
  let i := booleanProjectionIso B
  let η : ProjAlg (StepAlgebra B) → ℝ := fun p => ν (i.symm p)
  have hzero : η ⊥ = 0 := by simpa only [η, i.symm.map_bot] using hν.1.1
  have hadd (p q : ProjAlg (StepAlgebra B)) (hpq : Disjoint p q) :
      η (p ⊔ q) = η p + η q := by
    have hd : Disjoint (i.symm p) (i.symm q) := by
      apply disjoint_iff.mpr
      rw [← i.symm.map_inf, hpq.eq_bot, i.symm.map_bot]
    simpa only [η, i.symm.map_sup] using Gelfand39ValuationSup.disjoint_add ν hν.1 (i.symm p) (i.symm q) hd
  obtain ⟨Φ, hΦ, _⟩ := Step.positive_valuation_bounded_extension
    (boolean_step_projection_span_dense B) η hzero hadd (fun p => hpos _)
  have hval (p : B) : Φ (stepProjection B p) = (ν p : ℂ) := by
    change Φ (i p).val = (ν p : ℂ)
    rw [hΦ]
    simp only [η, i.symm_apply_apply]
  have hm : Φ ∈ StepPredual B := by
    change IsContinuousValuation (fun p => Φ (stepProjection B p))
    simp only [hval]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change (ν ⊥ : ℂ) = 0
      exact_mod_cast hν.1.1
    · intro p q
      change (ν p : ℂ) + (ν q : ℂ) = (ν (p ⊔ q) : ℂ) + (ν (p ⊓ q) : ℂ)
      exact_mod_cast hν.1.2 p q
    intro s a hs hd ha
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp (hν.2 s a hs hd ha)
  refine ⟨⟨Φ, hm⟩, hval, ?_, ?_⟩
  · change ‖Φ‖ ≤ ν ⊤
    have hn := Step.extension_opNorm_bound (boolean_step_projection_span_dense B)
      η hzero hadd (fun p => hpos _) Φ hΦ
    simpa only [η, i.symm.map_top] using hn
  · intro a ha
    exact Step.extension_nonneg (boolean_step_projection_span_dense B)
      η hzero hadd (fun p => hpos _) Φ hΦ ha

end
end Gelfand320
end Gelfand320WholeSource8

/- Source module Work.Gelfand320.ValuationBands; SHA256 c1e5e60b7d75ef6d417fc8e5d23daecf0e7822c342221a3cfcd60f3dc4dbd842. -/
section Gelfand320WholeSource9

set_option autoImplicit false
namespace Gelfand320
open Set Filter QAlgorithms.Papers.Independent.Support21.P20
open scoped Topology
noncomputable section
universe u
variable {B : Type u} [CompleteBooleanAlgebra B]

lemma continuous_valuation_band {R : Type*} [Zero R] [Add R] [TopologicalSpace R]
    (ν : B → R) (hν : IsContinuousValuation ν) (p : B) :
    IsContinuousValuation (fun b => ν (b ⊓ p)) := by
  refine ⟨⟨by simpa using hν.1.1, ?_⟩, ?_⟩
  · intro a b
    have hh := hν.1.2 (a ⊓ p) (b ⊓ p)
    rw [← inf_sup_right, ← inf_inf_distrib_right] at hh
    exact hh
  · intro s a hs hd ha
    let t : Set B := (fun b => b ⊓ p) '' s
    have ht : t.Nonempty := hs.image _
    have htd : DirectedOn (· ≤ ·) t := by
      rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
      obtain ⟨d, hd', hbd, hcd⟩ := hd b hb c hc
      exact ⟨d ⊓ p, ⟨d, hd', rfl⟩, inf_le_inf_right p hbd, inf_le_inf_right p hcd⟩
    have hta : IsLUB t (a ⊓ p) := by
      rw [ha.unique (isLUB_sSup s)]
      have he : sSup s ⊓ p = sSup t := by
        simp only [t, sSup_image, sSup_inf_eq]
      rw [he]
      exact isLUB_sSup t
    letI : Nonempty s := hs.to_subtype
    letI : Nonempty t := ht.to_subtype
    letI : IsDirectedOrder s := hd.isDirectedOrder
    letI : IsDirectedOrder t := htd.isDirectedOrder
    let k : s → t := fun b => ⟨b.val ⊓ p, b.val, b.property, rfl⟩
    have hk : Tendsto k atTop atTop := by
      apply tendsto_atTop.2
      rintro ⟨_, b, hb, rfl⟩
      filter_upwards [eventually_ge_atTop (⟨b, hb⟩ : s)] with c hc
      exact inf_le_inf_right p hc
    exact (hν.2 t (a ⊓ p) ht htd hta).comp hk

lemma nnreal_valuation_continuous (ν : B → NNReal)
    (hν : IsPositiveContinuousValuation ν) :
    IsContinuousValuation (fun b => (ν b : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · change (ν ⊥ : ℝ) = 0
    exact_mod_cast hν.1.1
  · intro a b
    change (ν a : ℝ) + (ν b : ℝ) = (ν (a ⊔ b) : ℝ) + (ν (a ⊓ b) : ℝ)
    exact_mod_cast hν.1.2 a b
  intro s a hs hd ha
  have hmono : Monotone (fun b : s => ν b.val) := fun b c hbc => hν.2.1 hbc
  have hl : IsLUB (Set.range (fun b : s => ν b.val)) (ν a) := by
    simpa only [Set.image_eq_range] using hν.2.2 s a hs hd ha
  exact NNReal.continuous_coe.continuousAt.tendsto.comp (tendsto_atTop_isLUB hmono hl)

end
end Gelfand320
end Gelfand320WholeSource9

/- Source module Work.Gelfand39JordanSource; SHA256 d42d3560b8be14075b9a9432cbc2621882fc317ee26982a17679a198bd23f907. -/
section Gelfand320WholeSource10

universe u
set_option autoImplicit false

/- Reused accepted proof by fizzyinc3, submission e058f284-c40d-45c0-b2f0-1f111145c267, as audited in accepted Gelfand lemma 3.11. Namespace and theorem body unchanged from that accepted source. -/

namespace Gelfand311Jordan
open QAlgorithms.Papers.Independent.Support21.P20

open Set Filter

open scoped NNReal Topology


section g72gk34
variable {L : Type*} [Order.Frame L]

def g72gk34_Pos (ν : L → ℝ) (a : L) : Prop := ∀ b : L, b ≤ a → 0 ≤ ν b

lemma g72gk34_le_compl {x y : L} (h : x ⊓ y = ⊥) : x ≤ yᶜ :=
  le_compl_iff_disjoint_right.mpr (disjoint_iff.mpr h)

lemma g72gk34_bot {ν : L → ℝ} (h : IsNormalValuation ν) : ν ⊥ = 0 := h.1.1.1

lemma g72gk34_disj {ν : L → ℝ} (h : IsNormalValuation ν) {x y : L} (hxy : x ⊓ y = ⊥) :
    ν (x ⊔ y) = ν x + ν y := by
  have := h.1.1.2 x y
  rw [hxy, g72gk34_bot h] at this
  linarith

lemma g72gk34_compl_eq {x b : L} (hx : x ≤ b) : (x ⊔ (b ⊓ xᶜ))ᶜ = bᶜ := by
  apply le_antisymm
  · rw [compl_sup]
    apply g72gk34_le_compl
    apply le_bot_iff.mp
    calc xᶜ ⊓ (b ⊓ xᶜ)ᶜ ⊓ b ≤ (b ⊓ xᶜ) ⊓ (b ⊓ xᶜ)ᶜ :=
          le_inf (le_inf inf_le_right (inf_le_left.trans inf_le_left))
            (inf_le_left.trans inf_le_right)
      _ = ⊥ := inf_compl_self _
  · exact compl_le_compl (sup_le hx inf_le_left)

lemma g72gk34_split {ν : L → ℝ} (h : IsNormalValuation ν) {x b : L} (hx : x ≤ b) :
    ν b = ν x + ν (b ⊓ xᶜ) := by
  have h1 : ν b = ν (x ⊔ (b ⊓ xᶜ)) := by
    rw [← h.2 b, ← g72gk34_compl_eq hx, h.2]
  rw [h1, g72gk34_disj h]
  apply le_bot_iff.mp
  calc x ⊓ (b ⊓ xᶜ) ≤ x ⊓ xᶜ := inf_le_inf_left _ inf_le_right
    _ = ⊥ := inf_compl_self _

lemma g72gk34_pos_bot (ν : L → ℝ) (h : IsNormalValuation ν) : g72gk34_Pos ν ⊥ := by
  intro b hb
  rw [le_bot_iff.mp hb, g72gk34_bot h]

lemma g72gk34_pos_sup {ν : L → ℝ} (h : IsNormalValuation ν) {a1 a2 : L}
    (h1 : g72gk34_Pos ν a1) (h2 : g72gk34_Pos ν a2) : g72gk34_Pos ν (a1 ⊔ a2) := by
  intro b hb
  set x := b ⊓ a1 with hxdef
  set y := b ⊓ xᶜ ⊓ a2 with hydef
  have e1 := g72gk34_split h (x := x) (b := b) inf_le_left
  have e2 := g72gk34_split h (x := y) (b := b ⊓ xᶜ) inf_le_left
  have hw : b ⊓ xᶜ ⊓ yᶜ = ⊥ := by
    apply le_bot_iff.mp
    have hw1 : b ⊓ xᶜ ⊓ yᶜ = (b ⊓ xᶜ ⊓ yᶜ) ⊓ (a1 ⊔ a2) :=
      (inf_eq_left.mpr ((inf_le_left.trans inf_le_left).trans hb)).symm
    rw [hw1, inf_sup_left]
    apply sup_le
    · calc b ⊓ xᶜ ⊓ yᶜ ⊓ a1 ≤ x ⊓ xᶜ :=
            le_inf (le_inf (inf_le_left.trans (inf_le_left.trans inf_le_left)) inf_le_right)
              (inf_le_left.trans (inf_le_left.trans inf_le_right))
        _ = ⊥ := inf_compl_self _
    · calc b ⊓ xᶜ ⊓ yᶜ ⊓ a2 ≤ y ⊓ yᶜ :=
            le_inf (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
              (inf_le_left.trans inf_le_right)
        _ = ⊥ := inf_compl_self _
  rw [hw, g72gk34_bot h] at e2
  have p1 : 0 ≤ ν x := h1 x inf_le_right
  have p2 : 0 ≤ ν y := h2 y inf_le_right
  linarith

lemma g72gk34_isDir {s : Set L} (hd : DirectedOn (· ≤ ·) s) : IsDirected s (· ≤ ·) :=
  ⟨fun x y => by
    obtain ⟨z, hz, h1, h2⟩ := hd x x.2 y y.2
    exact ⟨⟨z, hz⟩, h1, h2⟩⟩

lemma g72gk34_lim_ge {ν : L → ℝ} (h : IsNormalValuation ν) {s : Set L} {a : L}
    (hne : s.Nonempty) (hd : DirectedOn (· ≤ ·) s) (hl : IsLUB s a)
    (hp : ∀ b ∈ s, 0 ≤ ν b) : 0 ≤ ν a := by
  haveI : Nonempty s := hne.to_subtype
  haveI := g72gk34_isDir hd
  exact ge_of_tendsto' (h.1.2 s a hne hd hl) (fun b => hp b b.2)

lemma g72gk34_carrier_pos {ν : L → ℝ} (h : IsNormalValuation ν) :
    g72gk34_Pos ν (positiveCarrier ν) := by
  intro b hb
  let s : Set L := {z | ∃ a, g72gk34_Pos ν a ∧ z = b ⊓ a}
  apply g72gk34_lim_ge h (s := s) (a := b)
  · exact ⟨b ⊓ ⊥, ⊥, g72gk34_pos_bot ν h, rfl⟩
  · rintro _ ⟨a1, h1, rfl⟩ _ ⟨a2, h2, rfl⟩
    exact ⟨b ⊓ (a1 ⊔ a2), ⟨a1 ⊔ a2, g72gk34_pos_sup h h1 h2, rfl⟩,
      inf_le_inf_left _ le_sup_left, inf_le_inf_left _ le_sup_right⟩
  · constructor
    · rintro _ ⟨a, _, rfl⟩
      exact inf_le_left
    · intro u hu
      have : b = b ⊓ positiveCarrier ν := (inf_eq_left.mpr hb).symm
      rw [this, positiveCarrier, inf_sSup_eq]
      exact iSup₂_le fun a ha => hu ⟨a, ha, rfl⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact ha _ inf_le_right

lemma g72gk34_pos_iff {ν : L → ℝ} (h : IsNormalValuation ν) (a : L) :
    g72gk34_Pos ν a ↔ a ≤ positiveCarrier ν :=
  ⟨fun ha => le_sSup ha, fun ha b hb => g72gk34_carrier_pos h b (hb.trans ha)⟩

lemma g72gk34_choose {ν : L → ℝ} (h : IsNormalValuation ν) (r : L) :
    ∃ x ≤ r, ∀ y ≤ r, min 1 (-ν y) ≤ 2 * (-ν x) := by
  let S : Set ℝ := (fun y => min 1 (-ν y)) '' Set.Iic r
  have hS : BddAbove S := ⟨1, by rintro _ ⟨y, _, rfl⟩; exact min_le_left _ _⟩
  have hSn : S.Nonempty := ⟨_, r, le_refl r, rfl⟩
  by_cases hm : sSup S ≤ 0
  · refine ⟨⊥, bot_le, fun y hy => ?_⟩
    rw [g72gk34_bot h, neg_zero, mul_zero]
    exact (le_csSup hS ⟨y, hy, rfl⟩).trans hm
  · push_neg at hm
    obtain ⟨_, ⟨y0, hy0, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hSn (half_lt_self hm)
    refine ⟨y0, hy0, fun y hy => ?_⟩
    have h1 := le_csSup hS ⟨y, hy, rfl⟩
    have h2 : min 1 (-ν y0) ≤ -ν y0 := min_le_right _ _
    linarith

def g72gk34_seq (f : L → L) (b : L) : ℕ → L
  | 0 => ⊥
  | k + 1 => g72gk34_seq f b k ⊔ f (b ⊓ (g72gk34_seq f b k)ᶜ)

lemma g72gk34_exhaust {ν : L → ℝ} (h : IsNormalValuation ν) (b : L) :
    ∃ d ≤ b, g72gk34_Pos ν d ∧ ν b ≤ ν d := by
  choose f hf1 hf2 using g72gk34_choose h
  set X := g72gk34_seq f b with hXdef
  have hXs : ∀ k, X (k + 1) = X k ⊔ f (b ⊓ (X k)ᶜ) := fun k => rfl
  have hX0 : X 0 = ⊥ := rfl
  have hXb : ∀ k, X k ≤ b := by
    intro k
    induction k with
    | zero => rw [hX0]; exact bot_le
    | succ k ih => rw [hXs]; exact sup_le ih ((hf1 _).trans inf_le_left)
  have hmono : Monotone X := monotone_nat_of_le_succ fun k => by rw [hXs]; exact le_sup_left
  have hstep : ∀ k, ν (X (k + 1)) = ν (X k) + ν (f (b ⊓ (X k)ᶜ)) := by
    intro k
    rw [hXs, g72gk34_disj h]
    apply le_bot_iff.mp
    calc X k ⊓ f (b ⊓ (X k)ᶜ) ≤ X k ⊓ (X k)ᶜ :=
          inf_le_inf_left _ ((hf1 _).trans inf_le_right)
      _ = ⊥ := inf_compl_self _
  have hxneg : ∀ k, ν (f (b ⊓ (X k)ᶜ)) ≤ 0 := by
    intro k
    have := hf2 (b ⊓ (X k)ᶜ) ⊥ bot_le
    rw [g72gk34_bot h, neg_zero, min_eq_right zero_le_one] at this
    linarith
  have hXneg : ∀ k, ν (X k) ≤ 0 := by
    intro k
    induction k with
    | zero => rw [hX0, g72gk34_bot h]
    | succ k ih => rw [hstep]; linarith [hxneg k]
  set Xi := ⨆ k, X k with hXi
  have hXib : Xi ≤ b := iSup_le hXb
  have hdir : DirectedOn (· ≤ ·) (Set.range X) := directedOn_range.mpr (hmono.directed_le)
  have hlub : IsLUB (Set.range X) Xi := isLUB_iSup
  have hT := h.1.2 (Set.range X) Xi (Set.range_nonempty X) hdir hlub
  let g : ℕ → Set.range X := fun k => ⟨X k, k, rfl⟩
  have hg : Tendsto g atTop atTop := by
    rw [tendsto_atTop_atTop]
    rintro ⟨_, j, rfl⟩
    exact ⟨j, fun k hk => hmono hk⟩
  have hTX : Tendsto (fun k => ν (X k)) atTop (𝓝 (ν Xi)) := hT.comp hg
  have hTX1 : Tendsto (fun k => ν (X (k + 1))) atTop (𝓝 (ν Xi)) :=
    hTX.comp (tendsto_add_atTop_nat 1)
  have hx0 : Tendsto (fun k => 2 * (-ν (f (b ⊓ (X k)ᶜ)))) atTop (𝓝 0) := by
    have : Tendsto (fun k => 2 * (-(ν (X (k + 1)) - ν (X k)))) atTop
        (𝓝 (2 * (-(ν Xi - ν Xi)))) := ((hTX1.sub hTX).neg).const_mul 2
    rw [sub_self, neg_zero, mul_zero] at this
    refine this.congr fun k => ?_
    rw [hstep k]; ring
  have hXile : ν Xi ≤ 0 := le_of_tendsto' hTX hXneg
  refine ⟨b ⊓ Xiᶜ, inf_le_left, ?_, ?_⟩
  · intro y hy
    have hk : ∀ k, min 1 (-ν y) ≤ 2 * (-ν (f (b ⊓ (X k)ᶜ))) := fun k =>
      hf2 _ y (hy.trans (inf_le_inf_left _ (compl_le_compl (le_iSup X k))))
    have hle : min 1 (-ν y) ≤ 0 := ge_of_tendsto' hx0 hk
    by_contra hc
    push_neg at hc
    have : 0 < min 1 (-ν y) := lt_min one_pos (by linarith)
    linarith
  · have := g72gk34_split h hXib
    linarith

lemma g72gk34_negative {ν : L → ℝ} (h : IsNormalValuation ν) {c : L}
    (hc : c ⊓ positiveCarrier ν = ⊥) {b : L} (hb : b ≤ c) : ν b ≤ 0 := by
  obtain ⟨d, hdb, hdp, hle⟩ := g72gk34_exhaust h b
  have h1 : d ≤ positiveCarrier ν := le_sSup hdp
  have h2 : d = ⊥ := le_bot_iff.mp (hc ▸ le_inf (hdb.trans hb) h1)
  rw [h2, g72gk34_bot h] at hle
  exact hle

lemma g72gk34_neg {ν : L → ℝ} (h : IsNormalValuation ν) :
    IsNormalValuation (fun a => -ν a) := by
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · simp [g72gk34_bot h]
  · intro a b; have := h.1.1.2 a b; simp only; linarith
  · intro s a hne hd hl
    exact (h.1.2 s a hne hd hl).neg
  · intro a; simp only [h.2]

lemma g72gk34_regular {ν : L → ℝ} (h : IsNormalValuation ν) :
    (positiveCarrier ν)ᶜᶜ = positiveCarrier ν := by
  set P := positiveCarrier ν
  apply le_antisymm _ le_compl_compl
  apply le_sSup
  intro b hb
  have e := g72gk34_split h (x := b ⊓ P) (b := b) inf_le_left
  have hw : b ⊓ (b ⊓ P)ᶜ = ⊥ := by
    apply le_bot_iff.mp
    have hw1 : b ⊓ (b ⊓ P)ᶜ ≤ Pᶜ := by
      apply g72gk34_le_compl
      apply le_bot_iff.mp
      calc b ⊓ (b ⊓ P)ᶜ ⊓ P ≤ (b ⊓ P) ⊓ (b ⊓ P)ᶜ :=
            le_inf (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
              (inf_le_left.trans inf_le_right)
        _ = ⊥ := inf_compl_self _
    calc b ⊓ (b ⊓ P)ᶜ ≤ Pᶜ ⊓ Pᶜᶜ := le_inf hw1 (inf_le_left.trans hb)
      _ = ⊥ := inf_compl_self _
  rw [hw, g72gk34_bot h] at e
  have := g72gk34_carrier_pos h (b ⊓ P) inf_le_right
  linarith

lemma g72gk34_hahn {ν : L → ℝ} (h : IsNormalValuation ν) :
    (positiveCarrier ν ⊔ negativeCarrier ν)ᶜ = ⊥ := by
  set P := positiveCarrier ν
  set N := negativeCarrier ν
  set c := (P ⊔ N)ᶜ
  have hcP : c ⊓ P = ⊥ := by
    apply le_bot_iff.mp
    calc c ⊓ P ≤ Pᶜ ⊓ P := inf_le_inf_right _ (compl_le_compl le_sup_left)
      _ = ⊥ := compl_inf_self _
  have hcN : c ≤ N := by
    apply (g72gk34_pos_iff (g72gk34_neg h) c).mp
    intro b hb
    have := g72gk34_negative h hcP hb
    simp only; linarith
  apply le_bot_iff.mp
  calc c ≤ N ⊓ Nᶜ := le_inf hcN (compl_le_compl le_sup_right)
    _ = ⊥ := inf_compl_self _

lemma g72gk34_decomp {ν : L → ℝ} (h : IsNormalValuation ν) (a : L) :
    ν a = ν (positiveCarrier ν ⊓ a) + ν (negativeCarrier ν ⊓ a) := by
  set P := positiveCarrier ν
  set N := negativeCarrier ν
  have hQ := g72gk34_hahn h
  have h1 : ν a = ν ((P ⊔ N) ⊓ a) := by
    rw [← h.2 a, ← h.2 ((P ⊔ N) ⊓ a), compl_compl_inf_distrib, hQ, compl_bot, top_inf_eq]
  have h2 := h.1.1.2 (P ⊓ a) (N ⊓ a)
  rw [← inf_sup_right] at h2
  have hz1 : 0 ≤ ν (P ⊓ a ⊓ (N ⊓ a)) :=
    g72gk34_carrier_pos h _ (inf_le_left.trans inf_le_left)
  have hz2 : 0 ≤ -ν (P ⊓ a ⊓ (N ⊓ a)) :=
    g72gk34_carrier_pos (g72gk34_neg h) _ (inf_le_right.trans inf_le_left)
  linarith

lemma g72gk34_restrict {ν : L → ℝ} (h : IsNormalValuation ν) {Q : L} (hQ : Qᶜᶜ = Q) :
    IsNormalValuation (fun a => ν (Q ⊓ a)) := by
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · simp only [inf_bot_eq, g72gk34_bot h]
  · intro a b
    have := h.1.1.2 (Q ⊓ a) (Q ⊓ b)
    simp only
    rw [← inf_sup_left, ← inf_inf_distrib_left] at this
    exact this
  · intro s a hne hd hl
    let s' : Set L := (fun b => Q ⊓ b) '' s
    have hne' : s'.Nonempty := hne.image _
    have hd' : DirectedOn (· ≤ ·) s' := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      obtain ⟨z, hz, h1, h2⟩ := hd x hx y hy
      exact ⟨Q ⊓ z, ⟨z, hz, rfl⟩, inf_le_inf_left _ h1, inf_le_inf_left _ h2⟩
    have hl' : IsLUB s' (Q ⊓ a) := by
      constructor
      · rintro _ ⟨x, hx, rfl⟩
        exact inf_le_inf_left _ (hl.1 hx)
      · intro u hu
        rw [← hl.sSup_eq, inf_sSup_eq]
        exact iSup₂_le fun b hb => hu ⟨b, hb, rfl⟩
    have hT := h.1.2 s' (Q ⊓ a) hne' hd' hl'
    let g : s → s' := fun b => ⟨Q ⊓ b.1, b.1, b.2, rfl⟩
    haveI : Nonempty s := hne.to_subtype
    haveI := g72gk34_isDir hd
    have hg : Tendsto g atTop atTop := by
      rw [tendsto_atTop_atTop]
      rintro ⟨_, b0, hb0, rfl⟩
      exact ⟨⟨b0, hb0⟩, fun b hb => inf_le_inf_left _ hb⟩
    exact hT.comp hg
  · intro a
    simp only
    rw [← hQ, ← compl_compl_inf_distrib, h.2, hQ]

lemma g72gk34_bool_cc (hB : ∀ a : L, a ⊔ aᶜ = ⊤) (a : L) : aᶜᶜ = a := by
  apply le_antisymm _ le_compl_compl
  calc aᶜᶜ = aᶜᶜ ⊓ (a ⊔ aᶜ) := by rw [hB, inf_top_eq]
    _ = (aᶜᶜ ⊓ a) ⊔ (aᶜᶜ ⊓ aᶜ) := inf_sup_left _ _ _
    _ ≤ a := sup_le inf_le_right (by rw [compl_inf_self]; exact bot_le)

lemma g72gk34_HJ {ν : L → ℝ} (h : IsNormalValuation ν)
    (hPP : positiveCarrier ν ⊔ (positiveCarrier ν)ᶜ = ⊤) : HahnJordanConclusions ν := by
  have hn := g72gk34_neg h
  refine ⟨fun a => g72gk34_pos_iff h a, fun a => g72gk34_pos_iff hn a, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply top_le_iff.mp
    rw [← hPP]
    apply sup_le_sup_left
    apply (g72gk34_pos_iff hn _).mp
    intro b hb
    have := g72gk34_negative h (c := (positiveCarrier ν)ᶜ) (compl_inf_self _) hb
    simp only; linarith
  · intro a
    constructor
    · intro ha
      exact le_inf ((g72gk34_pos_iff h a).mp fun b hb => (ha b hb).ge)
        ((g72gk34_pos_iff hn a).mp fun b hb => by show 0 ≤ -ν b; rw [ha b hb, neg_zero])
    · intro ha b hb
      have h1 := g72gk34_carrier_pos h b (hb.trans (ha.trans inf_le_left))
      have h2 : 0 ≤ -ν b := g72gk34_carrier_pos hn b (hb.trans (ha.trans inf_le_right))
      linarith
  · exact g72gk34_restrict h (g72gk34_regular h)
  · exact g72gk34_restrict hn (g72gk34_regular hn)
  · intro a; exact g72gk34_carrier_pos h _ inf_le_left
  · intro a; exact g72gk34_carrier_pos hn _ inf_le_left
  · intro a
    have := g72gk34_decomp h a
    simp only [jordanPositive, jordanNegative]
    linarith

lemma g72gk34_regime {ν : L → ℝ} (h : IsJordanRegime ν) : HahnJordanConclusions ν := by
  rcases h with ⟨hS, hN⟩ | ⟨hB, hC⟩
  · apply g72gk34_HJ hN
    have := hS.2 (positiveCarrier ν)
    rw [g72gk34_regular hN, sup_comm] at this
    exact this
  · have hN : IsNormalValuation ν := ⟨hC, fun a => by rw [g72gk34_bool_cc hB a]⟩
    exact g72gk34_HJ hN (hB _)

end g72gk34

section g72gk34b
variable {L : Type*} [Order.Frame L]

lemma g72gk34_cmap {nu : L → ℂ} (φ : ℂ → ℝ) (hφ0 : φ 0 = 0)
    (hadd : ∀ x y, φ (x + y) = φ x + φ y) (hc : Continuous φ)
    (h : IsContinuousValuation nu) : IsContinuousValuation (fun a => φ (nu a)) :=
  ⟨⟨by simp only [h.1.1, hφ0], fun a b => by simp only; rw [← hadd, ← hadd, h.1.2 a b]⟩,
    fun s a hne hd hl => (hc.tendsto _).comp (h.2 s a hne hd hl)⟩

lemma g72gk34_nmap {nu : L → ℂ} (φ : ℂ → ℝ) (hφ0 : φ 0 = 0)
    (hadd : ∀ x y, φ (x + y) = φ x + φ y) (hc : Continuous φ)
    (h : IsNormalValuation nu) : IsNormalValuation (fun a => φ (nu a)) :=
  ⟨g72gk34_cmap φ hφ0 hadd hc h.1, fun a => by simp only [h.2]⟩

lemma g72gk34_rmap {nu : L → ℂ} (φ : ℂ → ℝ) (hφ0 : φ 0 = 0)
    (hadd : ∀ x y, φ (x + y) = φ x + φ y) (hc : Continuous φ)
    (h : IsJordanRegime nu) : IsJordanRegime (fun a => φ (nu a)) := by
  rcases h with ⟨hS, hN⟩ | ⟨hB, hC⟩
  · exact Or.inl ⟨hS, g72gk34_nmap φ hφ0 hadd hc hN⟩
  · exact Or.inr ⟨hB, g72gk34_cmap φ hφ0 hadd hc hC⟩

end g72gk34b

theorem hahnJordan_decomposition (L : Type u) [Order.Frame L] :
    (∀ nu : L → ℝ, IsJordanRegime nu → HahnJordanConclusions nu) ∧
    (∀ nu : L → ℂ, IsJordanRegime nu → ComplexJordanConclusions nu) := by
  refine ⟨fun nu h => g72gk34_regime h, fun nu h => ?_⟩
  have hre := g72gk34_rmap Complex.re Complex.zero_re Complex.add_re Complex.continuous_re h
  have him := g72gk34_rmap Complex.im Complex.zero_im Complex.add_im Complex.continuous_im h
  have H1 := g72gk34_regime hre
  have H2 := g72gk34_regime him
  unfold ComplexJordanConclusions
  intro re im
  refine ⟨H1, H2, fun a => ?_⟩
  have e1 := H1.2.2.2.2.2.2.2.2 a
  have e2 := H2.2.2.2.2.2.2.2.2 a
  apply Complex.ext
  · simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.sub_im, Complex.ofReal_im]
    simp only at e1
    linarith
  · simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.sub_re, Complex.ofReal_re]
    simp only at e2
    linarith

end Gelfand311Jordan
end Gelfand320WholeSource10

/- Source module Work.Gelfand320.StepBands; SHA256 f297a97cc0ad5212f124d33c38e04d0b76a2b594e4672e561df16b253d87380f. -/
section Gelfand320WholeSource11

set_option autoImplicit false
namespace Gelfand320
open Set GelfandVNA.Duality QAlgorithms.Papers.Independent.Support21.P20
open scoped ComplexOrder
noncomputable section
universe u
variable {B : Type u} [CompleteBooleanAlgebra B]

local instance : LE (ProjAlg (StepAlgebra B)) :=
  (inferInstance : BooleanAlgebra (ProjAlg (StepAlgebra B))).toPartialOrder.toLE
local instance : Preorder (ProjAlg (StepAlgebra B)) :=
  (inferInstance : BooleanAlgebra (ProjAlg (StepAlgebra B))).toPartialOrder.toPreorder
local instance : PartialOrder (ProjAlg (StepAlgebra B)) :=
  (inferInstance : BooleanAlgebra (ProjAlg (StepAlgebra B))).toPartialOrder

lemma stepProjection_inf (p q : B) :
    stepProjection B (p ⊓ q) = stepProjection B p * stepProjection B q := by
  dsimp [stepProjection]
  rw [(booleanProjectionIso B).map_inf]
  rfl

lemma stepProjection_top : stepProjection B (⊤ : B) = 1 := by
  dsimp [stepProjection]
  rw [(booleanProjectionIso B).map_top]
  rfl

lemma stepProjection_compl (p : B) :
    stepProjection B pᶜ = 1 - stepProjection B p := by
  dsimp [stepProjection]
  rw [map_compl (booleanProjectionIso B)]
  rfl

lemma stepPredual_ext {φ ψ : StepPredual B}
    (h : ∀ p, φ.val (stepProjection B p) = ψ.val (stepProjection B p)) : φ = ψ := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext_on (boolean_step_projection_span_dense B)
  rintro a ⟨p, rfl⟩
  obtain ⟨b, rfl⟩ := (booleanProjectionIso B).surjective p
  exact h b

/-- Positivity of a valuation functional is detected on Boolean projections. -/
def StepPositive (φ : StepPredual B) : Prop := ∀ p, 0 ≤ φ.val (stepProjection B p)

lemma stepPositive_real (φ : StepPredual B) (hφ : StepPositive φ) (p : B) :
    φ.val (stepProjection B p) = ((φ.val (stepProjection B p)).re : ℂ) := by
  apply Complex.ext
  · rfl
  · exact (Complex.nonneg_iff.mp (hφ p)).2.symm

lemma stepPositive_norm_le (φ : StepPredual B) (hφ : StepPositive φ) :
    ‖φ‖ ≤ (φ.val (stepProjection B ⊤)).re := by
  let ν : B → ℝ := fun p => (φ.val (stepProjection B p)).re
  have hc : IsContinuousValuation ν := Gelfand311Jordan.g72gk34_cmap Complex.re
    Complex.zero_re Complex.add_re Complex.continuous_re φ.property
  obtain ⟨ψ, hψ, hn, _⟩ := exists_positive_step_functional B ν hc
    (fun p => (Complex.nonneg_iff.mp (hφ p)).1)
  have he : φ = ψ := stepPredual_ext (fun p => (stepPositive_real φ hφ p).trans (hψ p).symm)
  calc
    ‖φ‖ = ‖ψ‖ := congrArg norm he
    _ ≤ ν ⊤ := hn

/-- Multiplication by a Boolean projection acts on the candidate predual. -/
def stepBand (φ : StepPredual B) (p : B) : StepPredual B :=
  ⟨φ.val.comp ((ContinuousLinearMap.mul ℂ (StepAlgebra B)).flip (stepProjection B p)), by
    change IsContinuousValuation (fun q => φ.val (stepProjection B q * stepProjection B p))
    simp only [← stepProjection_inf]
    exact continuous_valuation_band _ φ.property p⟩

lemma stepBand_apply (φ : StepPredual B) (p : B) (a : StepAlgebra B) :
    (stepBand φ p).val a = φ.val (a * stepProjection B p) := rfl

lemma stepBand_projection (φ : StepPredual B) (p q : B) :
    (stepBand φ p).val (stepProjection B q) = φ.val (stepProjection B (q ⊓ p)) := by
  rw [stepBand_apply, stepProjection_inf]

lemma stepBand_positive (φ : StepPredual B) (hφ : StepPositive φ) (p : B) :
    StepPositive (stepBand φ p) := by
  intro q
  rw [stepBand_projection]
  exact hφ _

lemma stepBand_norm_le (φ : StepPredual B) (hφ : StepPositive φ) (p : B) :
    ‖stepBand φ p‖ ≤ (φ.val (stepProjection B p)).re := by
  have hh := stepPositive_norm_le (stepBand φ p) (stepBand_positive φ hφ p)
  simpa only [stepBand_projection, top_inf_eq] using hh

lemma stepBand_top (φ : StepPredual B) : stepBand φ ⊤ = φ := by
  apply stepPredual_ext
  intro p
  rw [stepBand_projection, inf_top_eq]

lemma stepBand_compl (φ : StepPredual B) (p : B) : stepBand φ pᶜ = φ - stepBand φ p := by
  apply Subtype.ext
  ext a
  change φ.val (a * stepProjection B pᶜ) = φ.val a - φ.val (a * stepProjection B p)
  rw [stepProjection_compl, mul_sub, mul_one, map_sub]

lemma stepBand_band (φ : StepPredual B) (p q : B) :
    stepBand (stepBand φ p) q = stepBand φ (p ⊓ q) := by
  apply stepPredual_ext
  intro a
  simp only [stepBand_projection]
  congr 2
  ac_rfl

lemma stepBand_add (φ ψ : StepPredual B) (p : B) :
    stepBand (φ + ψ) p = stepBand φ p + stepBand ψ p := by
  apply stepPredual_ext
  intro q
  rfl

lemma stepBand_smul (c : ℂ) (φ : StepPredual B) (p : B) :
    stepBand (c • φ) p = c • stepBand φ p := by
  apply stepPredual_ext
  intro q
  rfl

end
end Gelfand320
end Gelfand320WholeSource11

/- Source module Work.Gelfand320.ValuationStepApproximation; SHA256 d2cd0c185e6e206953a2d7aec0bc4714e01814369d55c4d038182dabdb45d9f8. -/
section Gelfand320WholeSource12

set_option autoImplicit false
namespace Gelfand320
open Set QAlgorithms.Papers.Independent.Support21.P20
open scoped BigOperators
noncomputable section
universe u
variable {B : Type u} [CompleteBooleanAlgebra B]

/-- The largest Boolean carrier on which ν is bounded by t times μ. -/
def ratioCut (μ ν : B → ℝ) (t : ℝ) : B :=
  negativeCarrier (fun p => ν p - t * μ p)

lemma ratioCut_le (μ ν : B → ℝ) (hμ : IsContinuousValuation μ)
    (hν : IsContinuousValuation ν) (t : ℝ) (p : B) :
    p ≤ ratioCut μ ν t ↔ ∀ q, q ≤ p → ν q ≤ t * μ q := by
  have hH := (Gelfand311Jordan.hahnJordan_decomposition B).1 _
    (Or.inr ⟨fun _ => sup_compl_eq_top,
      Gelfand39ValuationSup.sub_const_mul_continuous μ ν hμ hν t⟩)
  constructor
  · intro hp q hq
    have hh := ((hH.2.1 p).2 hp) q hq
    change 0 ≤ -(ν q - t * μ q) at hh
    linarith
  · intro hp
    apply (hH.2.1 p).1
    intro q hq
    change 0 ≤ -(ν q - t * μ q)
    linarith [hp q hq]

lemma ratioCut_monotone (μ ν : B → ℝ) (hμ : IsContinuousValuation μ)
    (hν : IsContinuousValuation ν) (hμpos : ∀ p, 0 ≤ μ p) :
    Monotone (ratioCut μ ν) := by
  intro s t hst
  apply (ratioCut_le μ ν hμ hν t _).2
  intro p hp
  exact ((ratioCut_le μ ν hμ hν s _).1 le_rfl p hp).trans
    (mul_le_mul_of_nonneg_right hst (hμpos p))

lemma ratioCut_complement_lower (μ ν : B → ℝ) (hμ : IsContinuousValuation μ)
    (hν : IsContinuousValuation ν) (t : ℝ) (p : B)
    (hp : p ≤ (ratioCut μ ν t)ᶜ) : t * μ p ≤ ν p := by
  let d : B → ℝ := fun p => ν p - t * μ p
  have hH : HahnJordanConclusions d := (Gelfand311Jordan.hahnJordan_decomposition B).1 _
    (Or.inr ⟨fun _ => sup_compl_eq_top,
      Gelfand39ValuationSup.sub_const_mul_continuous μ ν hμ hν t⟩)
  have hcov : positiveCarrier d ⊔ negativeCarrier d = ⊤ := hH.2.2.1
  have hle : (negativeCarrier d)ᶜ ≤ positiveCarrier d := by
    calc
      (negativeCarrier d)ᶜ = (negativeCarrier d)ᶜ ⊓
          (positiveCarrier d ⊔ negativeCarrier d) := by rw [hcov, inf_top_eq]
      _ = ((negativeCarrier d)ᶜ ⊓ positiveCarrier d) ⊔
          ((negativeCarrier d)ᶜ ⊓ negativeCarrier d) := inf_sup_left _ _ _
      _ ≤ positiveCarrier d := sup_le inf_le_right (by simp)
  have hh := ((hH.1 p).2 (hp.trans hle)) p le_rfl
  change 0 ≤ ν p - t * μ p at hh
  linarith

lemma valuation_sum_slices (η : B → ℝ) (hη : IsContinuousValuation η)
    (q : ℕ → B) (hq : Monotone q) (N : ℕ) (p : B) :
    ∑ j ∈ Finset.range N, η (p ⊓ (q (j + 1) ⊓ (q j)ᶜ)) =
      η (p ⊓ q N) - η (p ⊓ q 0) := by
  have hn : IsNormalValuation η := ⟨hη, fun b => by rw [compl_compl]⟩
  induction N with
  | zero => simp
  | succ N ih =>
    have hh := Gelfand311Jordan.g72gk34_split hn
      (inf_le_inf_left p (hq (Nat.le_succ N)))
    have he : (p ⊓ q (N + 1)) ⊓ (p ⊓ q N)ᶜ = p ⊓ (q (N + 1) ⊓ (q N)ᶜ) := by
      rw [compl_inf, inf_sup_left]
      have hz : (p ⊓ q (N + 1)) ⊓ pᶜ = ⊥ := by
        calc
          _ = (p ⊓ pᶜ) ⊓ q (N + 1) := by ac_rfl
          _ = ⊥ := by simp
      rw [hz, bot_sup_eq]
      exact inf_assoc _ _ _
    rw [he] at hh
    rw [Finset.sum_range_succ, ih]
    linarith

/-- Dominated positive continuous valuations admit uniformly accurate finite
step densities in the dominating valuation. -/
theorem exists_valuation_step_approximation (μ ν : B → ℝ)
    (hμ : IsContinuousValuation μ) (hν : IsContinuousValuation ν)
    (hμpos : ∀ p, 0 ≤ μ p) (hνpos : ∀ p, 0 ≤ ν p)
    (C : ℝ) (hdom : ∀ p, ν p ≤ C * μ p) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∃ q : ℕ → B, Monotone q ∧ q N = ⊤ ∧
      ∀ p : B, 0 ≤ ν p - ∑ j ∈ Finset.range N, (j : ℝ) * δ * μ (p ⊓ (q (j + 1) ⊓ (q j)ᶜ)) ∧
        ν p - ∑ j ∈ Finset.range N, (j : ℝ) * δ * μ (p ⊓ (q (j + 1) ⊓ (q j)ᶜ)) ≤ δ * μ p := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_ge (C / δ)
  have hCN : C ≤ (N : ℝ) * δ := (div_le_iff₀ hδ).mp hN
  let q : ℕ → B := fun j => ratioCut μ ν ((j : ℝ) * δ)
  have hq : Monotone q := (ratioCut_monotone μ ν hμ hν hμpos).comp
    (fun i j hij => mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) hδ.le)
  have hqN : q N = ⊤ := by
    apply top_unique
    apply (ratioCut_le μ ν hμ hν ((N : ℝ) * δ) ⊤).2
    intro p hp
    exact (hdom p).trans (mul_le_mul_of_nonneg_right hCN (hμpos p))
  refine ⟨N, q, hq, hqN, ?_⟩
  intro p
  have hz : ν (p ⊓ q 0) = 0 := by
    apply le_antisymm _ (hνpos _)
    have hh := (ratioCut_le μ ν hμ hν 0 (q 0)).1 (by dsimp [q]; simp) (p ⊓ q 0) inf_le_right
    simpa only [zero_mul] using hh
  have hsν := valuation_sum_slices ν hν q hq N p
  rw [hqN, inf_top_eq, hz, sub_zero] at hsν
  have hsμ := valuation_sum_slices μ hμ q hq N p
  rw [hqN, inf_top_eq] at hsμ
  have hbounds (j : ℕ) :
      (j : ℝ) * δ * μ (p ⊓ (q (j + 1) ⊓ (q j)ᶜ)) ≤ ν (p ⊓ (q (j + 1) ⊓ (q j)ᶜ)) ∧
      ν (p ⊓ (q (j + 1) ⊓ (q j)ᶜ)) ≤ ((j : ℝ) + 1) * δ * μ (p ⊓ (q (j + 1) ⊓ (q j)ᶜ)) := by
    constructor
    · exact ratioCut_complement_lower μ ν hμ hν ((j : ℝ) * δ) _
        (inf_le_right.trans inf_le_right)
    · have hh := (ratioCut_le μ ν hμ hν (((j + 1 : ℕ) : ℝ) * δ) (q (j + 1))).1
        le_rfl (p ⊓ (q (j + 1) ⊓ (q j)ᶜ)) (inf_le_right.trans inf_le_left)
      simpa only [Nat.cast_add, Nat.cast_one] using hh
  rw [← hsν, ← Finset.sum_sub_distrib]
  constructor
  · exact Finset.sum_nonneg (fun j hj => sub_nonneg.mpr (hbounds j).1)
  · calc
      _ ≤ ∑ j ∈ Finset.range N, δ * μ (p ⊓ (q (j + 1) ⊓ (q j)ᶜ)) := by
        apply Finset.sum_le_sum
        intro j hj
        have hh := (hbounds j).2
        nlinarith
      _ = δ * (μ p - μ (p ⊓ q 0)) := by rw [← Finset.mul_sum, hsμ]
      _ ≤ δ * μ p := mul_le_mul_of_nonneg_left (sub_le_self _ (hμpos _)) hδ.le

end
end Gelfand320
end Gelfand320WholeSource12

/- Source module Work.Gelfand39Truncation; SHA256 05045be01afdd9354bb64d65bc3c06ac889d78f9076ca7bdb5331405f2f99a39. -/
section Gelfand320WholeSource13

set_option autoImplicit false
noncomputable section
open Set

namespace Gelfand39Truncation
universe u
variable {B : Type u} [CompleteBooleanAlgebra B]

/-- Maximal negative carriers of ν-(n+1)μ increase with n. -/
theorem monotone_carriers (μ ν : B → ℝ) (hμpos : ∀ a, 0 ≤ μ a)
    (q : ℕ → B)
    (hneg : ∀ (n : ℕ) a, a ≤ q n → ν a ≤ ((n : ℝ) + 1) * μ a)
    (hmax : ∀ (n : ℕ) r, (∀ a, a ≤ r → ν a ≤ ((n : ℝ) + 1) * μ a) → r ≤ q n) :
    Monotone q := by
  intro n m hnm
  apply hmax m (q n)
  intro a ha
  exact (hneg n a ha).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hnm 1)
    (hμpos a))

/-- Absolute continuity forces the union of the dominated carrier pieces to
have full ν-measure. No ambient strict positivity of μ is required. -/
theorem carrier_sup_full (μ ν : B → ℝ)
    (hμpos : ∀ a, 0 ≤ μ a) (hμmono : Monotone μ) (hνmono : Monotone ν)
    (hνsplit : ∀ a, ν a + ν aᶜ = ν ⊤)
    (hac : ∀ a, μ a = 0 → ν a = 0)
    (q : ℕ → B)
    (hbound : ∀ n : ℕ, ((n : ℝ) + 1) * μ (q n)ᶜ ≤ ν (q n)ᶜ) :
    ν (iSup q) = ν ⊤ := by
  have hμnull : μ (iSup q)ᶜ = 0 := by
    by_contra hne
    have hpos : 0 < μ (iSup q)ᶜ :=
      lt_of_le_of_ne (hμpos _) (Ne.symm hne)
    obtain ⟨n, hn⟩ := exists_nat_gt (ν ⊤ / μ (iSup q)ᶜ)
    have hstrict : ν ⊤ < (n : ℝ) * μ (iSup q)ᶜ := (div_lt_iff₀ hpos).mp hn
    have hle : μ (iSup q)ᶜ ≤ μ (q n)ᶜ :=
      hμmono (compl_le_compl (le_iSup q n))
    have hcap : (n : ℝ) * μ (iSup q)ᶜ ≤ ν ⊤ := by
      calc
        (n : ℝ) * μ (iSup q)ᶜ ≤ ((n : ℝ) + 1) * μ (iSup q)ᶜ :=
          mul_le_mul_of_nonneg_right (by linarith) hpos.le
        _ ≤ ((n : ℝ) + 1) * μ (q n)ᶜ :=
          mul_le_mul_of_nonneg_left hle (by positivity)
        _ ≤ ν (q n)ᶜ := hbound n
        _ ≤ ν ⊤ := hνmono le_top
    exact (not_lt_of_ge hcap) hstrict
  have hνnull := hac _ hμnull
  have h := hνsplit (iSup q)
  rw [hνnull, add_zero] at h
  exact h

/-- Finite directed-supremum continuity turns full carrier measure into
arbitrarily small positive tails, the estimate needed for norm approximation. -/
theorem exists_small_complement (ν : B → ℝ) (q : ℕ → B)
    (hνsplit : ∀ a, ν a + ν aᶜ = ν ⊤)
    (hfull : ν (iSup q) = ν ⊤)
    (hSup : IsLUB (ν '' Set.range q) (ν (iSup q)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n, ν (q n)ᶜ < ε := by
  by_contra h
  push_neg at h
  have hle : ν (iSup q) ≤ ν ⊤ - ε := hSup.2 (by
    rintro y ⟨b, ⟨n, rfl⟩, rfl⟩
    have hn := h n
    have hs := hνsplit (q n)
    linarith)
  rw [hfull] at hle
  linarith

end Gelfand39Truncation
end
end Gelfand320WholeSource13

/- Source module Work.Gelfand39TruncationCarriers; SHA256 be2b6ae9e5364908500fe0259be1173dd398e10eb9008ca5c346c6b6c62e5764. -/
section Gelfand320WholeSource14

set_option autoImplicit false
noncomputable section
open Set QAlgorithms.Papers.Independent.Support21.P20

namespace Gelfand39Truncation
universe u
variable {B : Type u} [CompleteBooleanAlgebra B]

def carrier (μ ν : B → ℝ) (n : ℕ) : B :=
  negativeCarrier (fun a => ν a - ((n : ℝ) + 1) * μ a)

theorem carrier_bound (μ ν : B → ℝ)
    (hHahn : ∀ n : ℕ, HahnJordanConclusions
      (fun a => ν a - ((n : ℝ) + 1) * μ a))
    (n : ℕ) (a : B) (ha : a ≤ carrier μ ν n) :
    ν a ≤ ((n : ℝ) + 1) * μ a := by
  have h := ((hHahn n).2.1 (carrier μ ν n)).2 le_rfl a ha
  change 0 ≤ -(ν a - ((n : ℝ) + 1) * μ a) at h
  linarith

theorem carrier_maximal (μ ν : B → ℝ)
    (hHahn : ∀ n : ℕ, HahnJordanConclusions
      (fun a => ν a - ((n : ℝ) + 1) * μ a))
    (n : ℕ) (r : B)
    (hr : ∀ a, a ≤ r → ν a ≤ ((n : ℝ) + 1) * μ a) :
    r ≤ carrier μ ν n := by
  apply ((hHahn n).2.1 r).1
  intro a ha
  change 0 ≤ -(ν a - ((n : ℝ) + 1) * μ a)
  linarith [hr a ha]

theorem carrier_complement_bound (μ ν : B → ℝ)
    (hHahn : ∀ n : ℕ, HahnJordanConclusions
      (fun a => ν a - ((n : ℝ) + 1) * μ a)) (n : ℕ) :
    ((n : ℝ) + 1) * μ (carrier μ ν n)ᶜ ≤ ν (carrier μ ν n)ᶜ := by
  let d : B → ℝ := fun a => ν a - ((n : ℝ) + 1) * μ a
  have hcover : positiveCarrier d ⊔ negativeCarrier d = ⊤ := (hHahn n).2.2.1
  have hle : (negativeCarrier d)ᶜ ≤ positiveCarrier d := by
    calc
      (negativeCarrier d)ᶜ =
          (negativeCarrier d)ᶜ ⊓ (positiveCarrier d ⊔ negativeCarrier d) := by
        rw [hcover, inf_top_eq]
      _ = ((negativeCarrier d)ᶜ ⊓ positiveCarrier d) ⊔
          ((negativeCarrier d)ᶜ ⊓ negativeCarrier d) :=
        inf_sup_left (negativeCarrier d)ᶜ (positiveCarrier d) (negativeCarrier d)
      _ ≤ positiveCarrier d := sup_le inf_le_right (by simp)
  have h := ((hHahn n).1 (negativeCarrier d)ᶜ).2 hle _ le_rfl
  change 0 ≤ ν (carrier μ ν n)ᶜ - ((n : ℝ) + 1) * μ (carrier μ ν n)ᶜ at h
  linarith

/-- Hahn carriers give dominated truncations with arbitrarily small ν-tails. -/
theorem exists_small_carrier_complement (μ ν : B → ℝ)
    (hμpos : ∀ a, 0 ≤ μ a) (hμmono : Monotone μ) (hνmono : Monotone ν)
    (hνsplit : ∀ a, ν a + ν aᶜ = ν ⊤)
    (hac : ∀ a, μ a = 0 → ν a = 0)
    (hHahn : ∀ n : ℕ, HahnJordanConclusions
      (fun a => ν a - ((n : ℝ) + 1) * μ a))
    (hSup : ∀ s : Set B, s.Nonempty → DirectedOn (· ≤ ·) s →
      IsLUB (ν '' s) (ν (sSup s))) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ν (carrier μ ν n)ᶜ < ε := by
  let q : ℕ → B := carrier μ ν
  have hmono : Monotone q := monotone_carriers μ ν hμpos q
    (carrier_bound μ ν hHahn) (carrier_maximal μ ν hHahn)
  have hfull : ν (iSup q) = ν ⊤ := carrier_sup_full μ ν hμpos hμmono hνmono
    hνsplit hac q (carrier_complement_bound μ ν hHahn)
  apply exists_small_complement ν q hνsplit hfull
  · simpa only [sSup_range] using
      hSup (Set.range q) (Set.range_nonempty q) (directedOn_range.mpr hmono.directed_le)
  · exact hε

end Gelfand39Truncation
end
end Gelfand320WholeSource14

/- Source module Work.Gelfand320.StepDomination; SHA256 e915e3354ade1f126a8d70284f7b8360f71835b26ab981aeef4d78d87ea1423e. -/
section Gelfand320WholeSource15

set_option autoImplicit false
namespace Gelfand320
open Set GelfandVNA.Duality QAlgorithms.Papers.Independent.Support21.P20
open scoped ComplexOrder BigOperators
noncomputable section
universe u
variable {B : Type u} [CompleteBooleanAlgebra B]

def stepValuation (φ : StepPredual B) (p : B) : ℝ := (φ.val (stepProjection B p)).re

lemma stepValuation_add (φ ψ : StepPredual B) (p : B) :
    stepValuation (φ + ψ) p = stepValuation φ p + stepValuation ψ p := Complex.add_re _ _

lemma stepValuation_real_smul (c : ℝ) (φ : StepPredual B) (p : B) :
    stepValuation (c • φ) p = c * stepValuation φ p := by
  change (c • φ.val (stepProjection B p)).re = _
  exact Complex.smul_re c _

lemma stepValuation_continuous (φ : StepPredual B) : IsContinuousValuation (stepValuation φ) :=
  Gelfand311Jordan.g72gk34_cmap Complex.re Complex.zero_re Complex.add_re
    Complex.continuous_re φ.property

lemma stepValuation_nonneg (φ : StepPredual B) (hφ : StepPositive φ) (p : B) :
    0 ≤ stepValuation φ p := (Complex.nonneg_iff.mp (hφ p)).1

/-- Every closed positive cone containing the bands of a positive valuation
contains all positive valuations dominated by it. The finite approximants are
formed from Hahn ratio cuts, not from an assumed Radon–Nikodym derivative. -/
theorem step_dominated_mem_closed_cone (φ ψ : StepPredual B)
    (hφ : StepPositive φ) (hψ : StepPositive ψ) (C : ℝ)
    (hdom : ∀ p, stepValuation ψ p ≤ C * stepValuation φ p)
    (K : Set (StepPredual B)) (hK : IsClosed K) (hzero : 0 ∈ K)
    (hadd : ∀ x ∈ K, ∀ y ∈ K, x + y ∈ K)
    (hsmul : ∀ c : ℝ, 0 ≤ c → ∀ x ∈ K, c • x ∈ K)
    (hband : ∀ p, stepBand φ p ∈ K) : ψ ∈ K := by
  classical
  rw [← hK.closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let M := stepValuation φ ⊤
  have hM : 0 ≤ M := stepValuation_nonneg φ hφ ⊤
  let δ : ℝ := ε / (M + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  obtain ⟨N, q, hq, hqN, hb⟩ := exists_valuation_step_approximation
    (stepValuation φ) (stepValuation ψ) (stepValuation_continuous φ)
    (stepValuation_continuous ψ) (stepValuation_nonneg φ hφ)
    (stepValuation_nonneg ψ hψ) C hdom δ hδ
  let ζ : StepPredual B := ∑ j ∈ Finset.range N,
    ((j : ℝ) * δ) • stepBand φ (q (j + 1) ⊓ (q j)ᶜ)
  have hz (p : B) : ζ.val (stepProjection B p) =
      ((∑ j ∈ Finset.range N, (j : ℝ) * δ *
        stepValuation φ (p ⊓ (q (j + 1) ⊓ (q j)ᶜ)) : ℝ) : ℂ) := by
    change stepEvaluation B (stepProjection B p) ζ = _
    dsimp only [ζ]
    rw [map_sum, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [LinearMapClass.map_smul_of_tower, stepEvaluation_apply, stepBand_projection,
      stepPositive_real φ hφ]
    simp only [stepValuation, Complex.ofReal_mul, Complex.real_smul]
  have hres : StepPositive (ψ - ζ) := by
    intro p
    change 0 ≤ ψ.val (stepProjection B p) - ζ.val (stepProjection B p)
    rw [hz, stepPositive_real ψ hψ p, ← Complex.ofReal_sub]
    exact Complex.nonneg_iff.mpr ⟨(hb p).1, rfl⟩
  have hnorm : ‖ψ - ζ‖ ≤ δ * M := by
    calc
      _ ≤ ((ψ - ζ).val (stepProjection B ⊤)).re := stepPositive_norm_le _ hres
      _ = stepValuation ψ ⊤ - ∑ j ∈ Finset.range N, (j : ℝ) * δ *
          stepValuation φ (⊤ ⊓ (q (j + 1) ⊓ (q j)ᶜ)) := by
        change (ψ.val (stepProjection B ⊤) - ζ.val (stepProjection B ⊤)).re = _
        rw [hz, Complex.sub_re, Complex.ofReal_re]
        rfl
      _ ≤ δ * M := (hb ⊤).2
  have hsum (s : Finset ℕ) :
      (∑ j ∈ s, ((j : ℝ) * δ) • stepBand φ (q (j + 1) ⊓ (q j)ᶜ)) ∈ K := by
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | @insert j s hj ih =>
      rw [Finset.sum_insert hj]
      exact hadd _ (hsmul _ (mul_nonneg (Nat.cast_nonneg j) hδ.le) _ (hband _)) _ ih
  have hζ : ζ ∈ K := hsum _
  refine ⟨ζ, hζ, ?_⟩
  rw [dist_eq_norm]
  apply hnorm.trans_lt
  have he : δ * (M + 1) = ε := div_mul_cancel₀ ε (by linarith : M + 1 ≠ 0)
  nlinarith

/-- Absolute continuity suffices for the same closed-cone conclusion, by the
checked Hahn-carrier truncation theorem and vanishing positive tails. -/
theorem step_absolutelyContinuous_mem_closed_cone (φ ψ : StepPredual B)
    (hφ : StepPositive φ) (hψ : StepPositive ψ)
    (hac : ∀ p, stepValuation φ p = 0 → stepValuation ψ p = 0)
    (K : Set (StepPredual B)) (hK : IsClosed K) (hzero : 0 ∈ K)
    (hadd : ∀ x ∈ K, ∀ y ∈ K, x + y ∈ K)
    (hsmul : ∀ c : ℝ, 0 ≤ c → ∀ x ∈ K, c • x ∈ K)
    (hband : ∀ p, stepBand φ p ∈ K) : ψ ∈ K := by
  let μ := stepValuation φ
  let ν := stepValuation ψ
  have hμ := stepValuation_continuous φ
  have hν := stepValuation_continuous ψ
  have hμpos := stepValuation_nonneg φ hφ
  have hνpos := stepValuation_nonneg ψ hψ
  have hμmono := Gelfand39ValuationSup.monotone_of_positive μ hμ.1 hμpos
  have hνmono := Gelfand39ValuationSup.monotone_of_positive ν hν.1 hνpos
  have hνsplit (p : B) : ν p + ν pᶜ = ν ⊤ := by
    have hh := hν.1.2 p pᶜ
    simpa only [sup_compl_eq_top, inf_compl_eq_bot, hν.1.1, add_zero] using hh
  have hHahn (n : ℕ) : HahnJordanConclusions (fun p => ν p - ((n : ℝ) + 1) * μ p) :=
    (Gelfand311Jordan.hahnJordan_decomposition B).1 _
      (Or.inr ⟨fun _ => sup_compl_eq_top,
        Gelfand39ValuationSup.sub_const_mul_continuous μ ν hμ hν _⟩)
  rw [← hK.closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨n, hn⟩ := Gelfand39Truncation.exists_small_carrier_complement μ ν
    hμpos hμmono hνmono hνsplit hac hHahn
    (Gelfand39ValuationSup.isLUB_image ν hν hνpos) ε hε
  let p := Gelfand39Truncation.carrier μ ν n
  have hpK : stepBand ψ p ∈ K := by
    apply step_dominated_mem_closed_cone φ (stepBand ψ p) hφ
      (stepBand_positive ψ hψ p) ((n : ℝ) + 1) _ K hK hzero hadd hsmul hband
    intro q
    change ((stepBand ψ p).val (stepProjection B q)).re ≤ ((n : ℝ) + 1) * μ q
    rw [stepBand_projection]
    exact (Gelfand39Truncation.carrier_bound μ ν hHahn n (q ⊓ p) inf_le_right).trans
      (mul_le_mul_of_nonneg_left (hμmono inf_le_left) (by positivity))
  refine ⟨stepBand ψ p, hpK, ?_⟩
  rw [dist_eq_norm, ← stepBand_compl]
  exact (stepBand_norm_le ψ hψ pᶜ).trans_lt hn


end
end Gelfand320
end Gelfand320WholeSource15

/- Source module Work.Gelfand320.StepBandContinuity; SHA256 0a4a1bbbb2917404a87ec54df5fe7ea5599630953655b352b8869f91603f5427. -/
section Gelfand320WholeSource16

set_option autoImplicit false
namespace Gelfand320
open Set Filter GelfandVNA.Duality QAlgorithms.Papers.Independent.Support21.P20
open scoped Topology ComplexOrder
noncomputable section
universe u
variable {B : Type u} [CompleteBooleanAlgebra B]

lemma stepBand_sub_of_le (φ : StepPredual B) {p a : B} (hp : p ≤ a) :
    stepBand φ a - stepBand φ p = stepBand φ (a ⊓ pᶜ) := by
  have he : stepProjection B a * stepProjection B p = stepProjection B p := by
    rw [← stepProjection_inf, inf_eq_right.mpr hp]
  apply Subtype.ext
  ext x
  change φ.val (x * stepProjection B a) - φ.val (x * stepProjection B p) =
    φ.val (x * stepProjection B (a ⊓ pᶜ))
  rw [stepProjection_inf, stepProjection_compl, mul_sub, mul_one, he, mul_sub, map_sub]

lemma stepBand_sub_norm_le (φ : StepPredual B) (hφ : StepPositive φ)
    {p a : B} (hp : p ≤ a) :
    ‖stepBand φ a - stepBand φ p‖ ≤ stepValuation φ a - stepValuation φ p := by
  have he := stepBand_sub_of_le φ hp
  have hv : stepValuation φ (a ⊓ pᶜ) = stepValuation φ a - stepValuation φ p := by
    have hh := congrArg (fun ψ : StepPredual B => (ψ.val (stepProjection B ⊤)).re) he
    change ((stepBand φ a).val (stepProjection B ⊤) -
      (stepBand φ p).val (stepProjection B ⊤)).re =
      ((stepBand φ (a ⊓ pᶜ)).val (stepProjection B ⊤)).re at hh
    simpa only [stepBand_projection, top_inf_eq, Complex.sub_re, stepValuation] using hh.symm
  rw [he, ← hv]
  exact stepBand_norm_le φ hφ _

/-- Positive valuation bands converge in norm along every directed Boolean supremum. -/
theorem stepBand_tendsto (φ : StepPredual B) (hφ : StepPositive φ)
    (s : Set B) (a : B) (hs : s.Nonempty) (hd : DirectedOn (· ≤ ·) s) (ha : IsLUB s a) :
    Tendsto (fun p : s => stepBand φ p.val) atTop (𝓝 (stepBand φ a)) := by
  have ht := (stepValuation_continuous φ).2 s a hs hd ha
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [(Metric.tendsto_nhds.mp ht) ε hε] with p hp
  rw [dist_eq_norm, norm_sub_rev]
  apply (stepBand_sub_norm_le φ hφ (ha.1 p.property)).trans_lt
  calc
    stepValuation φ a - stepValuation φ p.val ≤
        |stepValuation φ a - stepValuation φ p.val| := le_abs_self _
    _ < ε := by simpa only [Real.dist_eq, abs_sub_comm] using hp

/-- Evaluating positive bands by a bounded real linear functional gives an actual
continuous Boolean valuation. -/
theorem bandFunctional_isContinuousValuation (R : StepPredual B →L[ℝ] ℝ)
    (φ : StepPredual B) (hφ : StepPositive φ) :
    IsContinuousValuation (fun p => R (stepBand φ p)) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hz : stepBand φ ⊥ = 0 := by
      apply stepPredual_ext
      intro p
      rw [stepBand_projection, inf_bot_eq]
      exact φ.property.1.1
    change R (stepBand φ ⊥) = 0
    rw [hz, map_zero]
  · intro p q
    have he : stepBand φ p + stepBand φ q = stepBand φ (p ⊔ q) + stepBand φ (p ⊓ q) := by
      apply stepPredual_ext
      intro r
      change (stepBand φ p).val (stepProjection B r) + (stepBand φ q).val (stepProjection B r) =
        (stepBand φ (p ⊔ q)).val (stepProjection B r) + (stepBand φ (p ⊓ q)).val (stepProjection B r)
      simp only [stepBand_projection]
      have hh := φ.property.1.2 (r ⊓ p) (r ⊓ q)
      rw [← inf_sup_left, ← inf_inf_distrib_left] at hh
      exact hh
    simpa only [map_add] using congrArg R he
  · intro s a hs hd ha
    exact R.continuous.continuousAt.tendsto.comp (stepBand_tendsto φ hφ s a hs hd ha)

end
end Gelfand320
end Gelfand320WholeSource16

/- Source module Work.Gelfand39FaithfulValuation; SHA256 a6e7c4a5a11460e52e760cbb13007f9d19911b906cb3272025e78c3d0c80768c. -/
section Gelfand320WholeSource17

set_option autoImplicit false
noncomputable section
open Set

namespace Gelfand39FaithfulValuation
universe u
variable {B : Type u} [CompleteBooleanAlgebra B]

/-- Faithfulness makes a finite positive valuation strictly increasing. -/
theorem strictMono_of_faithful (ν : B → ℝ) (hzero : ν ⊥ = 0)
    (hadd : ∀ a b, ν a + ν b = ν (a ⊔ b) + ν (a ⊓ b))
    (hpos : ∀ a, 0 ≤ ν a) (hfaithful : ∀ a, ν a = 0 → a = ⊥) :
    StrictMono ν := by
  intro a b hab
  let d := b ⊓ aᶜ
  have hd : d ≠ ⊥ := by
    intro hd
    have hba : b ≤ a := by
      calc
        b = b ⊓ (a ⊔ aᶜ) := by simp
        _ = (b ⊓ a) ⊔ (b ⊓ aᶜ) := inf_sup_left b a aᶜ
        _ = b ⊓ a := by change (b ⊓ a) ⊔ d = b ⊓ a; rw [hd, sup_bot_eq]
        _ ≤ a := inf_le_right
    exact (not_le_of_gt hab) hba
  have hdpos : 0 < ν d := lt_of_le_of_ne (hpos d) (by
    intro h
    exact hd (hfaithful d h.symm))
  have hunion : a ⊔ d = b := by
    dsimp [d]
    rw [sup_inf_left, sup_eq_right.mpr hab.le, sup_compl_eq_top, inf_top_eq]
  have hinter : a ⊓ d = ⊥ := by
    dsimp [d]
    calc
      a ⊓ (b ⊓ aᶜ) = (a ⊓ aᶜ) ⊓ b := by ac_rfl
      _ = ⊥ := by simp
  have h := hadd a d
  rw [hunion, hinter, hzero] at h
  linarith

/-- Directed-supremum continuity makes the supremum of all null elements null. -/
theorem null_sup_null (ν : B → ℝ) (hzero : ν ⊥ = 0)
    (hadd : ∀ a b, ν a + ν b = ν (a ⊔ b) + ν (a ⊓ b))
    (hpos : ∀ a, 0 ≤ ν a)
    (hSup : ∀ s : Set B, s.Nonempty → DirectedOn (· ≤ ·) s →
      IsLUB (ν '' s) (ν (sSup s))) :
    ν (sSup {b : B | ν b = 0}) = 0 := by
  let s : Set B := {b | ν b = 0}
  have hs : s.Nonempty := ⟨⊥, hzero⟩
  have hd : DirectedOn (· ≤ ·) s := by
    intro a ha b hb
    have h := hadd a b
    change ν a = 0 at ha
    change ν b = 0 at hb
    rw [ha, hb] at h
    have hjoin : ν (a ⊔ b) = 0 := by
      have h₁ := hpos (a ⊔ b)
      have h₂ := hpos (a ⊓ b)
      linarith
    exact ⟨a ⊔ b, hjoin, le_sup_left, le_sup_right⟩
  have hle : ν (sSup s) ≤ 0 := (hSup s hs hd).2 (by
    rintro y ⟨b, hb, rfl⟩
    exact le_of_eq hb)
  exact le_antisymm hle (hpos _)

/-- The complement of the maximal null element is a faithful principal part. -/
theorem faithful_on_null_complement (ν : B → ℝ) (hpos : ∀ a, 0 ≤ ν a)
    (hmono : Monotone ν)
    (hnull : ν (sSup {b : B | ν b = 0}) = 0)
    (b : B) (hb : b ≤ (sSup {c : B | ν c = 0})ᶜ) (hbzero : ν b = 0) :
    b = ⊥ := by
  let n : B := sSup {c : B | ν c = 0}
  have hn : b ≤ n := le_sSup hbzero
  exact bot_unique ((le_inf hn hb).trans (by simp [n]))

/-- Nullity is exactly membership below the maximal null element. -/
theorem null_iff_le_null_sup (ν : B → ℝ) (hpos : ∀ a, 0 ≤ ν a)
    (hmono : Monotone ν) (hnull : ν (sSup {b : B | ν b = 0}) = 0) (b : B) :
    ν b = 0 ↔ b ≤ sSup {c : B | ν c = 0} := by
  constructor
  · intro hb
    exact le_sSup hb
  · intro hb
    exact le_antisymm ((hmono hb).trans_eq hnull) (hpos b)

end Gelfand39FaithfulValuation
end
end Gelfand320WholeSource17

/- Source module Work.Gelfand320.StepSupport; SHA256 ad438bbac2dfb00e867a3c73416c27a31d3f474df9abce546859d364fd17c982. -/
section Gelfand320WholeSource18

set_option autoImplicit false
namespace Gelfand320
open Set GelfandVNA.Duality QAlgorithms.Papers.Independent.Support21.P20
noncomputable section
universe u
variable {B : Type u} [CompleteBooleanAlgebra B]

def stepSupport (φ : StepPredual B) : B := (sSup {p : B | stepValuation φ p = 0})ᶜ

lemma stepValuation_null_sup (φ : StepPredual B) (hφ : StepPositive φ) :
    stepValuation φ (sSup {p : B | stepValuation φ p = 0}) = 0 :=
  Gelfand39FaithfulValuation.null_sup_null _ (stepValuation_continuous φ).1.1
    (stepValuation_continuous φ).1.2 (stepValuation_nonneg φ hφ)
    (Gelfand39ValuationSup.isLUB_image _ (stepValuation_continuous φ) (stepValuation_nonneg φ hφ))

lemma stepValuation_null_iff (φ : StepPredual B) (hφ : StepPositive φ) (p : B) :
    stepValuation φ p = 0 ↔ Disjoint p (stepSupport φ) := by
  rw [stepSupport, disjoint_compl_right_iff]
  exact Gelfand39FaithfulValuation.null_iff_le_null_sup _ (stepValuation_nonneg φ hφ)
    (Gelfand39ValuationSup.monotone_of_positive _ (stepValuation_continuous φ).1
      (stepValuation_nonneg φ hφ)) (stepValuation_null_sup φ hφ) p

lemma stepBand_zero_iff (φ : StepPredual B) (hφ : StepPositive φ) (p : B) :
    stepBand φ p = 0 ↔ stepValuation φ p = 0 := by
  constructor
  · intro he
    have hh := congrArg (fun ψ : StepPredual B => (ψ.val (stepProjection B ⊤)).re) he
    change ((stepBand φ p).val (stepProjection B ⊤)).re = 0 at hh
    rw [stepBand_projection, top_inf_eq] at hh
    exact hh
  · intro hp
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    exact (stepBand_norm_le φ hφ p).trans_eq hp

lemma stepBand_support (φ : StepPredual B) (hφ : StepPositive φ) :
    stepBand φ (stepSupport φ) = φ := by
  have hz : stepBand φ (stepSupport φ)ᶜ = 0 := by
    apply (stepBand_zero_iff φ hφ _).2
    simpa only [stepSupport, compl_compl] using stepValuation_null_sup φ hφ
  rw [stepBand_compl, sub_eq_zero] at hz
  exact hz.symm

lemma stepSupport_band_le (φ : StepPredual B) (hφ : StepPositive φ) (p : B) :
    stepSupport (stepBand φ p) ≤ p := by
  have hz : stepValuation (stepBand φ p) pᶜ = 0 := by
    dsimp [stepValuation]
    rw [stepBand_projection, compl_inf_self]
    exact congrArg Complex.re φ.property.1.1
  have hh := (stepValuation_null_iff _ (stepBand_positive φ hφ p) pᶜ).1 hz
  simpa only [compl_compl] using hh.le_compl_left

lemma stepSupport_eq_bot_iff (φ : StepPredual B) (hφ : StepPositive φ) :
    stepSupport φ = ⊥ ↔ φ = 0 := by
  constructor
  · intro he
    rw [← stepBand_support φ hφ, he]
    exact (stepBand_zero_iff φ hφ ⊥).2 (stepValuation_continuous φ).1.1
  · intro he
    subst φ
    simp [stepSupport, stepValuation]

lemma supportBand_absolutelyContinuous (φ ψ : StepPredual B)
    (hφ : StepPositive φ) (p : B) (hp : stepValuation φ p = 0) :
    stepValuation (stepBand ψ (stepSupport φ)) p = 0 := by
  have hd := (stepValuation_null_iff φ hφ p).1 hp
  dsimp [stepValuation]
  rw [stepBand_projection, hd.eq_bot]
  exact congrArg Complex.re ψ.property.1.1

end
end Gelfand320
end Gelfand320WholeSource18

/- Source module Work.Gelfand320.UniversalCut; SHA256 4a00e0fc2ba4cc3bc9ec8db68465fbdc2b5c49283c9228bd3111e6fd3ff28fa2. -/
section Gelfand320WholeSource19

set_option autoImplicit false
namespace Gelfand320
open Set Filter GelfandVNA.Duality QAlgorithms.Papers.Independent.Support21.P20
open scoped Topology
noncomputable section
universe u
variable {B : Type u} [CompleteBooleanAlgebra B]

/-- A universal upper spectral band, tested against every positive valuation. -/
def CutAdmissible (R : StepPredual B →L[ℝ] ℝ) (t : ℝ) (p : B) : Prop :=
  ∀ φ : StepPredual B, StepPositive φ → R (stepBand φ p) ≤ t * stepValuation φ p

def universalCut (R : StepPredual B →L[ℝ] ℝ) (t : ℝ) : B :=
  sSup {p | CutAdmissible R t p}

lemma stepValuation_band (φ : StepPredual B) (p q : B) :
    stepValuation (stepBand φ p) q = stepValuation φ (q ⊓ p) := by
  dsimp [stepValuation]
  rw [stepBand_projection]

lemma cutAdmissible_bot (R : StepPredual B →L[ℝ] ℝ) (t : ℝ) : CutAdmissible R t ⊥ := by
  intro φ hφ
  rw [(stepBand_zero_iff φ hφ ⊥).2 (stepValuation_continuous φ).1.1, map_zero,
    (stepValuation_continuous φ).1.1, mul_zero]

lemma cutAdmissible_mono (R : StepPredual B →L[ℝ] ℝ) (t : ℝ)
    {p q : B} (hpq : p ≤ q) (hq : CutAdmissible R t q) : CutAdmissible R t p := by
  intro φ hφ
  have hh := hq (stepBand φ p) (stepBand_positive φ hφ p)
  simpa only [stepBand_band, inf_eq_left.mpr hpq, stepValuation_band,
    inf_eq_right.mpr hpq] using hh

lemma cutAdmissible_sup (R : StepPredual B →L[ℝ] ℝ) (t : ℝ)
    {p q : B} (hp : CutAdmissible R t p) (hq : CutAdmissible R t q) :
    CutAdmissible R t (p ⊔ q) := by
  intro φ hφ
  let d : B → ℝ := fun a => R (stepBand φ a) - t * stepValuation φ a
  have hd : IsContinuousValuation d := Gelfand39ValuationSup.sub_const_mul_continuous
    _ _ (stepValuation_continuous φ) (bandFunctional_isContinuousValuation R φ hφ) t
  have hn : IsNormalValuation d := ⟨hd, fun _ => by rw [compl_compl]⟩
  have hs := Gelfand311Jordan.g72gk34_split hn (show p ≤ p ⊔ q from le_sup_left)
  have he : (p ⊔ q) ⊓ pᶜ = q ⊓ pᶜ := by rw [inf_sup_right, inf_compl_eq_bot, bot_sup_eq]
  rw [he] at hs
  have h₁ := hp φ hφ
  have h₂ := cutAdmissible_mono R t (show q ⊓ pᶜ ≤ q from inf_le_left) hq φ hφ
  dsimp [d] at hs
  linarith

lemma universalCut_admissible (R : StepPredual B →L[ℝ] ℝ) (t : ℝ) :
    CutAdmissible R t (universalCut R t) := by
  let s : Set B := {p | CutAdmissible R t p}
  have hs : s.Nonempty := ⟨⊥, cutAdmissible_bot R t⟩
  have hd : DirectedOn (· ≤ ·) s := fun p hp q hq =>
    ⟨p ⊔ q, cutAdmissible_sup R t hp hq, le_sup_left, le_sup_right⟩
  letI : Nonempty s := hs.to_subtype
  letI : IsDirectedOrder s := hd.isDirectedOrder
  intro φ hφ
  have hr := R.continuous.continuousAt.tendsto.comp (stepBand_tendsto φ hφ s (sSup s) hs hd (isLUB_sSup s))
  have hv := ((stepValuation_continuous φ).2 s (sSup s) hs hd (isLUB_sSup s)).const_mul t
  exact le_of_tendsto_of_tendsto' hr hv (fun p => p.property φ hφ)

lemma universalCut_le_iff (R : StepPredual B →L[ℝ] ℝ) (t : ℝ) (p : B) :
    p ≤ universalCut R t ↔ CutAdmissible R t p :=
  ⟨fun h => cutAdmissible_mono R t h (universalCut_admissible R t), fun h => le_sSup h⟩

lemma universalCut_monotone (R : StepPredual B →L[ℝ] ℝ) : Monotone (universalCut R) := by
  intro s t hst
  apply (universalCut_le_iff R t _).2
  intro φ hφ
  exact (universalCut_admissible R s φ hφ).trans
    (mul_le_mul_of_nonneg_right hst (stepValuation_nonneg φ hφ _))

/-- Bounds on all bands of a positive valuation propagate to its entire
support. Null regions are excluded by using the support, rather than a maximal
Hahn carrier containing arbitrary common-null regions. -/
lemma stepSupport_admissible (R : StepPredual B →L[ℝ] ℝ) (t : ℝ)
    (φ : StepPredual B) (hφ : StepPositive φ)
    (hb : ∀ p, R (stepBand φ p) ≤ t * stepValuation φ p) :
    CutAdmissible R t (stepSupport φ) := by
  let K : Set (StepPredual B) := {ψ | R ψ ≤ t * stepValuation ψ ⊤}
  have hK : IsClosed K := by
    have hc : Continuous (fun ψ : StepPredual B => stepValuation ψ ⊤) := by
      change Continuous (fun ψ => (stepEvaluation B (stepProjection B ⊤) ψ).re)
      fun_prop
    exact isClosed_le R.continuous (continuous_const.mul hc)
  have hzero : 0 ∈ K := by simp [K, stepValuation]
  have hadd : ∀ x ∈ K, ∀ y ∈ K, x + y ∈ K := by
    intro x hx y hy
    change R x ≤ t * stepValuation x ⊤ at hx
    change R y ≤ t * stepValuation y ⊤ at hy
    change R (x + y) ≤ t * stepValuation (x + y) ⊤
    rw [map_add, stepValuation_add, mul_add]
    exact add_le_add hx hy
  have hsmul : ∀ c : ℝ, 0 ≤ c → ∀ x ∈ K, c • x ∈ K := by
    intro c hc x hx
    change R x ≤ t * stepValuation x ⊤ at hx
    change R (c • x) ≤ t * stepValuation (c • x) ⊤
    rw [map_smul, stepValuation_real_smul]
    simpa only [smul_eq_mul, mul_left_comm] using mul_le_mul_of_nonneg_left hx hc
  have hband (p : B) : stepBand φ p ∈ K := by
    change R (stepBand φ p) ≤ t * stepValuation (stepBand φ p) ⊤
    rw [stepValuation_band, top_inf_eq]
    exact hb p
  intro ψ hψ
  have hh := step_absolutelyContinuous_mem_closed_cone φ (stepBand ψ (stepSupport φ)) hφ
    (stepBand_positive ψ hψ _) (supportBand_absolutelyContinuous φ ψ hφ)
    K hK hzero hadd hsmul hband
  change R (stepBand ψ (stepSupport φ)) ≤
    t * stepValuation (stepBand ψ (stepSupport φ)) ⊤ at hh
  simpa only [stepValuation_band, top_inf_eq] using hh

/-- The complement of a universal upper cut carries the opposite lower bound. -/
theorem universalCut_complement_lower (R : StepPredual B →L[ℝ] ℝ) (t : ℝ)
    (φ : StepPredual B) (hφ : StepPositive φ) (p : B)
    (hp : p ≤ (universalCut R t)ᶜ) : t * stepValuation φ p ≤ R (stepBand φ p) := by
  by_contra hn
  have hneg : R (stepBand φ p) - t * stepValuation φ p < 0 := sub_neg.mpr (lt_of_not_ge hn)
  let d : B → ℝ := fun q => R (stepBand φ q) - t * stepValuation φ q
  have hd : IsContinuousValuation d := Gelfand39ValuationSup.sub_const_mul_continuous
    _ _ (stepValuation_continuous φ) (bandFunctional_isContinuousValuation R φ hφ) t
  have hH : HahnJordanConclusions d := (Gelfand311Jordan.hahnJordan_decomposition B).1 _
    (Or.inr ⟨fun _ => sup_compl_eq_top, hd⟩)
  let a := p ⊓ negativeCarrier d
  let η := stepBand φ a
  have hη : StepPositive η := stepBand_positive φ hφ a
  have hnegCarrier := hH.2.1
  obtain ⟨_, _, _, _, _, _, hpositive, _, hdecomp⟩ := hH
  have hsplit := hdecomp p
  have hplus := hpositive p
  have hnegative : d a < 0 := by
    change d p = d (positiveCarrier d ⊓ p) - (-d (negativeCarrier d ⊓ p)) at hsplit
    change 0 ≤ d (positiveCarrier d ⊓ p) at hplus
    rw [inf_comm (positiveCarrier d) p, inf_comm (negativeCarrier d) p] at hsplit
    rw [inf_comm (positiveCarrier d) p] at hplus
    change d p < 0 at hneg
    dsimp [a]
    linarith
  have hηbound (q : B) : R (stepBand η q) ≤ t * stepValuation η q := by
    have hh := ((hnegCarrier (negativeCarrier d)).2 le_rfl) (q ⊓ a)
      (inf_le_right.trans inf_le_right)
    change 0 ≤ -d (q ⊓ a) at hh
    change R (stepBand (stepBand φ a) q) ≤ t * stepValuation (stepBand φ a) q
    rw [stepBand_band, stepValuation_band, inf_comm a q]
    dsimp [d] at hh
    linarith
  have hcut : stepSupport η ≤ universalCut R t :=
    (universalCut_le_iff R t _).2 (stepSupport_admissible R t η hη hηbound)
  have hle : stepSupport η ≤ (universalCut R t)ᶜ :=
    (stepSupport_band_le φ hφ a).trans (inf_le_left.trans hp)
  have hs0 : stepSupport η = ⊥ := bot_unique ((le_inf hcut hle).trans (by simp))
  have hη0 := (stepSupport_eq_bot_iff η hη).1 hs0
  have hηmass : stepValuation φ a = 0 := (stepBand_zero_iff φ hφ a).1 hη0
  change R η - t * stepValuation φ a < 0 at hnegative
  rw [hη0, map_zero, hηmass, mul_zero, sub_zero] at hnegative
  exact lt_irrefl _ hnegative


end
end Gelfand320
end Gelfand320WholeSource19

/- Source module Work.Gelfand320.StepJordan; SHA256 b9f094da790fa6ff259153589d41e14c8dc7ac804a186af0e36904cfc13d4f29. -/
section Gelfand320WholeSource20

set_option autoImplicit false
namespace Gelfand320
open Set GelfandVNA.Duality QAlgorithms.Papers.Independent.Support21.P20
open scoped ComplexOrder
noncomputable section
universe u
variable {B : Type u} [CompleteBooleanAlgebra B]

lemma step_projection_evaluation_norm_le (φ : StepPredual B) (p : B) :
    ‖φ.val (stepProjection B p)‖ ≤ ‖φ‖ := by
  calc
    _ ≤ ‖φ.val‖ * ‖stepProjection B p‖ := φ.val.le_opNorm _
    _ ≤ ‖φ‖ := by
      change ‖φ.val‖ * ‖stepProjection B p‖ ≤ ‖φ.val‖
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (stepProjection_norm B p) (norm_nonneg φ.val)

lemma stepValuation_le_norm (φ : StepPredual B) (p : B) :
    stepValuation φ p ≤ ‖φ‖ :=
  (Complex.re_le_norm _).trans (step_projection_evaluation_norm_le φ p)

lemma exists_real_step_jordan (ν : B → ℝ) (hν : IsContinuousValuation ν)
    (C : ℝ) (hb : ∀ p, |ν p| ≤ C) :
    ∃ φ ψ : StepPredual B, StepPositive φ ∧ StepPositive ψ ∧
      ‖φ‖ ≤ C ∧ ‖ψ‖ ≤ C ∧
      ∀ p, (ν p : ℂ) = φ.val (stepProjection B p) - ψ.val (stepProjection B p) := by
  obtain ⟨_, _, _, _, hP, hN, hp, hn, hsplit⟩ :=
    (Gelfand311Jordan.hahnJordan_decomposition B).1 ν
      (Or.inr ⟨fun _ => sup_compl_eq_top, hν⟩)
  obtain ⟨φ, hφ, hφnorm, _⟩ := exists_positive_step_functional B (jordanPositive ν) hP.1 hp
  obtain ⟨ψ, hψ, hψnorm, _⟩ := exists_positive_step_functional B (jordanNegative ν) hN.1 hn
  refine ⟨φ, ψ, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    rw [hφ]
    exact Complex.nonneg_iff.mpr ⟨hp p, rfl⟩
  · intro p
    rw [hψ]
    exact Complex.nonneg_iff.mpr ⟨hn p, rfl⟩
  · apply hφnorm.trans
    change ν (positiveCarrier ν ⊓ ⊤) ≤ C
    exact (le_abs_self _).trans (hb _)
  · apply hψnorm.trans
    change -ν (negativeCarrier ν ⊓ ⊤) ≤ C
    exact (neg_le_abs _).trans (hb _)
  · intro p
    rw [hφ, hψ, ← Complex.ofReal_sub, hsplit]

/-- Four positive members of the candidate predual reconstruct every member,
with each norm bounded by the norm of the original member. -/
theorem exists_complex_step_jordan (φ : StepPredual B) :
    ∃ φ₁ φ₂ φ₃ φ₄ : StepPredual B,
      StepPositive φ₁ ∧ StepPositive φ₂ ∧ StepPositive φ₃ ∧ StepPositive φ₄ ∧
      ‖φ₁‖ ≤ ‖φ‖ ∧ ‖φ₂‖ ≤ ‖φ‖ ∧ ‖φ₃‖ ≤ ‖φ‖ ∧ ‖φ₄‖ ≤ ‖φ‖ ∧
      φ = φ₁ - φ₂ + Complex.I • (φ₃ - φ₄) := by
  have hre := stepValuation_continuous φ
  have him : IsContinuousValuation (fun p => (φ.val (stepProjection B p)).im) :=
    Gelfand311Jordan.g72gk34_cmap Complex.im Complex.zero_im Complex.add_im
      Complex.continuous_im φ.property
  obtain ⟨φ₁, φ₂, h₁, h₂, hb₁, hb₂, he₁⟩ := exists_real_step_jordan
    (stepValuation φ) hre ‖φ‖ (fun p =>
      (Complex.abs_re_le_norm _).trans (step_projection_evaluation_norm_le φ p))
  obtain ⟨φ₃, φ₄, h₃, h₄, hb₃, hb₄, he₂⟩ := exists_real_step_jordan
    (fun p => (φ.val (stepProjection B p)).im) him ‖φ‖ (fun p =>
      (Complex.abs_im_le_norm _).trans (step_projection_evaluation_norm_le φ p))
  refine ⟨φ₁, φ₂, φ₃, φ₄, h₁, h₂, h₃, h₄, hb₁, hb₂, hb₃, hb₄, ?_⟩
  apply stepPredual_ext
  intro p
  change φ.val (stepProjection B p) = φ₁.val (stepProjection B p) - φ₂.val (stepProjection B p) +
    Complex.I * (φ₃.val (stepProjection B p) - φ₄.val (stepProjection B p))
  rw [← he₁, ← he₂]
  exact (Complex.re_add_im _).symm.trans (by simp only [stepValuation]; ring)

/-- Control on positive valuations controls the entire dual operator norm. -/
theorem step_dual_norm_bound (F : StepPredual B →L[ℂ] ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hb : ∀ φ : StepPredual B, StepPositive φ → ‖F φ‖ ≤ δ * stepValuation φ ⊤) :
    ‖F‖ ≤ 4 * δ := by
  apply F.opNorm_le_bound (by positivity)
  intro φ
  obtain ⟨φ₁, φ₂, φ₃, φ₄, h₁, h₂, h₃, h₄, hb₁, hb₂, hb₃, hb₄, he⟩ :=
    exists_complex_step_jordan φ
  have hbound (ψ : StepPredual B) (hψ : StepPositive ψ) (hn : ‖ψ‖ ≤ ‖φ‖) :
      ‖F ψ‖ ≤ δ * ‖φ‖ :=
    (hb ψ hψ).trans (mul_le_mul_of_nonneg_left ((stepValuation_le_norm ψ ⊤).trans hn) hδ)
  have hFe : F φ = F φ₁ - F φ₂ + Complex.I • (F φ₃ - F φ₄) := by
    rw [he, map_add, map_sub, map_smul, map_sub]
  rw [hFe]
  calc
    _ ≤ ‖F φ₁ - F φ₂‖ + ‖Complex.I • (F φ₃ - F φ₄)‖ := norm_add_le _ _
    _ ≤ (‖F φ₁‖ + ‖F φ₂‖) + (‖F φ₃‖ + ‖F φ₄‖) := by
      rw [norm_smul, Complex.norm_I, one_mul]
      exact add_le_add (norm_sub_le _ _) (norm_sub_le _ _)
    _ ≤ 4 * δ * ‖φ‖ := by
      have h1 := hbound φ₁ h₁ hb₁
      have h2 := hbound φ₂ h₂ hb₂
      have h3 := hbound φ₃ h₃ hb₃
      have h4 := hbound φ₄ h₄ hb₄
      linarith

end
end Gelfand320
end Gelfand320WholeSource20

/- Source module Work.Gelfand320.UniversalStepApproximation; SHA256 42c3c9208f8c0bcd93e44367a1795aea830beca3d9380ad33fd177443d143a6f. -/
section Gelfand320WholeSource21

set_option autoImplicit false
namespace Gelfand320
open Set GelfandVNA.Duality QAlgorithms.Papers.Independent.Support21.P20
open scoped BigOperators
noncomputable section
universe u
variable {B : Type u} [CompleteBooleanAlgebra B]

/-- Universal cuts supply a single finite step function approximating a positive
real functional simultaneously on every positive valuation. -/
theorem exists_positive_dual_step (R : StepPredual B →L[ℝ] ℝ)
    (hR : ∀ φ : StepPredual B, StepPositive φ → 0 ≤ R φ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ a : StepAlgebra B, ∀ φ : StepPredual B, StepPositive φ →
      |R φ - (φ.val a).re| ≤ δ * stepValuation φ ⊤ ∧ (φ.val a).im = 0 := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_ge (‖R‖ / δ)
  have hRN : ‖R‖ ≤ (N : ℝ) * δ := (div_le_iff₀ hδ).mp hN
  let q : ℕ → B := fun j => universalCut R ((j : ℝ) * δ)
  have hq : Monotone q := (universalCut_monotone R).comp
    (fun i j hij => mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) hδ.le)
  have hqN : q N = ⊤ := by
    apply top_unique
    apply (universalCut_le_iff R ((N : ℝ) * δ) ⊤).2
    intro φ hφ
    rw [stepBand_top]
    calc
      R φ ≤ ‖R φ‖ := le_abs_self _
      _ ≤ ‖R‖ * ‖φ‖ := R.le_opNorm _
      _ ≤ ‖R‖ * stepValuation φ ⊤ :=
        mul_le_mul_of_nonneg_left (stepPositive_norm_le φ hφ) (norm_nonneg _)
      _ ≤ (N : ℝ) * δ * stepValuation φ ⊤ :=
        mul_le_mul_of_nonneg_right hRN (stepValuation_nonneg φ hφ _)
  let a : StepAlgebra B := ∑ j ∈ Finset.range N,
    (((j : ℝ) * δ : ℝ) : ℂ) • stepProjection B (q (j + 1) ⊓ (q j)ᶜ)
  refine ⟨a, ?_⟩
  intro φ hφ
  let ν : B → ℝ := fun p => R (stepBand φ p)
  let μ := stepValuation φ
  have hν := bandFunctional_isContinuousValuation R φ hφ
  have hμ := stepValuation_continuous φ
  have hνpos (p : B) : 0 ≤ ν p := hR _ (stepBand_positive φ hφ p)
  have hμpos := stepValuation_nonneg φ hφ
  have hz : ν (q 0) = 0 := by
    apply le_antisymm _ (hνpos _)
    have hh := universalCut_admissible R 0 φ hφ
    simpa only [q, Nat.cast_zero, zero_mul] using hh
  have hsν := valuation_sum_slices ν hν q hq N ⊤
  simp only [top_inf_eq, hqN, hz, sub_zero] at hsν
  have hsμ := valuation_sum_slices μ hμ q hq N ⊤
  simp only [top_inf_eq, hqN] at hsμ
  have heval : φ.val a = ((∑ j ∈ Finset.range N, (j : ℝ) * δ *
      μ (q (j + 1) ⊓ (q j)ᶜ) : ℝ) : ℂ) := by
    rw [show a = ∑ j ∈ Finset.range N, (((j : ℝ) * δ : ℝ) : ℂ) •
      stepProjection B (q (j + 1) ⊓ (q j)ᶜ) from rfl, map_sum, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [map_smul, stepPositive_real φ hφ]
    simp only [μ, stepValuation, Complex.ofReal_mul, smul_eq_mul]
  have hbounds (j : ℕ) :
      (j : ℝ) * δ * μ (q (j + 1) ⊓ (q j)ᶜ) ≤ ν (q (j + 1) ⊓ (q j)ᶜ) ∧
      ν (q (j + 1) ⊓ (q j)ᶜ) ≤ ((j : ℝ) + 1) * δ * μ (q (j + 1) ⊓ (q j)ᶜ) := by
    constructor
    · exact universalCut_complement_lower R ((j : ℝ) * δ) φ hφ _ inf_le_right
    · have hh := cutAdmissible_mono R (((j + 1 : ℕ) : ℝ) * δ)
        (show q (j + 1) ⊓ (q j)ᶜ ≤ q (j + 1) from inf_le_left)
        (universalCut_admissible R _) φ hφ
      simpa only [Nat.cast_add, Nat.cast_one] using hh
  rw [heval, Complex.ofReal_re, Complex.ofReal_im]
  refine ⟨?_, rfl⟩
  have hνtop : ν ⊤ = R φ := by dsimp [ν]; rw [stepBand_top]
  rw [← hνtop, ← hsν, ← Finset.sum_sub_distrib]
  have hnonneg : 0 ≤ ∑ j ∈ Finset.range N,
      (ν (q (j + 1) ⊓ (q j)ᶜ) - (j : ℝ) * δ * μ (q (j + 1) ⊓ (q j)ᶜ)) :=
    Finset.sum_nonneg (fun j hj => sub_nonneg.mpr (hbounds j).1)
  rw [abs_of_nonneg hnonneg]
  calc
    _ ≤ ∑ j ∈ Finset.range N, δ * μ (q (j + 1) ⊓ (q j)ᶜ) := by
      apply Finset.sum_le_sum
      intro j hj
      have hh := (hbounds j).2
      nlinarith
    _ = δ * (μ ⊤ - μ (q 0)) := by rw [← Finset.mul_sum, hsμ]
    _ ≤ δ * μ ⊤ := mul_le_mul_of_nonneg_left (sub_le_self _ (hμpos _)) hδ.le

/-- A scalar shift reduces an arbitrary bounded real functional to the positive
case, without assuming a predual representation. -/
theorem exists_real_dual_step (R : StepPredual B →L[ℝ] ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ a : StepAlgebra B, ∀ φ : StepPredual B, StepPositive φ →
      |R φ - (φ.val a).re| ≤ δ * stepValuation φ ⊤ ∧ (φ.val a).im = 0 := by
  let M : StepPredual B →L[ℝ] ℝ := Complex.reCLM.comp
    ((stepEvaluation B (stepProjection B ⊤)).restrictScalars ℝ)
  have hM (φ : StepPredual B) : M φ = stepValuation φ ⊤ := rfl
  let T : StepPredual B →L[ℝ] ℝ := R + ‖R‖ • M
  have hT (φ : StepPredual B) : T φ = R φ + ‖R‖ * stepValuation φ ⊤ := rfl
  have hTpos (φ : StepPredual B) (hφ : StepPositive φ) : 0 ≤ T φ := by
    rw [hT]
    have hb := R.le_opNorm φ
    have hn := stepPositive_norm_le φ hφ
    have hc := mul_le_mul_of_nonneg_left hn (norm_nonneg R)
    have hneg := neg_le_abs (R φ)
    rw [Real.norm_eq_abs] at hb
    change ‖R‖ * ‖φ‖ ≤ ‖R‖ * stepValuation φ ⊤ at hc
    linarith
  obtain ⟨a, ha⟩ := exists_positive_dual_step T hTpos δ hδ
  refine ⟨a - (‖R‖ : ℂ) • 1, ?_⟩
  intro φ hφ
  have hφone : φ.val 1 = ((stepValuation φ ⊤ : ℝ) : ℂ) := by
    rw [← stepProjection_top (B := B)]
    exact stepPositive_real φ hφ ⊤
  have he : φ.val (a - (‖R‖ : ℂ) • 1) =
      φ.val a - ((‖R‖ * stepValuation φ ⊤ : ℝ) : ℂ) := by
    rw [map_sub, map_smul, hφone]
    simp only [Complex.ofReal_mul, smul_eq_mul]
  rw [he, Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
  refine ⟨?_, (ha φ hφ).2⟩
  have heq : R φ - ((φ.val a).re - ‖R‖ * stepValuation φ ⊤) = T φ - (φ.val a).re := by
    rw [hT]
    ring
  rw [heq]
  exact (ha φ hφ).1


end
end Gelfand320
end Gelfand320WholeSource21

/- Source module Work.Gelfand273.LocalizableCriterion; SHA256 70c0f69267e9958eca2d4419a8e19a7b57f6d0882dedb56ab1d586cc36825546. -/
section Gelfand320WholeSource22
/- Reused accepted proof by fizzyinc3, submission e4ac8c1d-3289-4144-baeb-8ddb71a3176f. Only a wrapper namespace and theorem name change. -/

namespace Gelfand273Criterion

open QAlgorithms.Papers.Independent.Support21.P20

open Set Filter

open scoped NNReal

universe u v

theorem g67c_restrict {A : Type u} [CompleteBooleanAlgebra A] (nu : A → ℝ≥0)
    (hnu : IsPositiveContinuousValuation nu) (a : A) :
    IsPositiveContinuousValuation (fun x : Set.Iic a => nu x.val) := by
  obtain ⟨⟨hbot, hmod⟩, hmono, hcont⟩ := hnu
  refine ⟨⟨hbot, fun x y => hmod x.val y.val⟩, fun x y hxy => hmono hxy, ?_⟩
  intro s b hsne hdir hlub
  have hl : IsLUB (Subtype.val '' s) b.val := by
    constructor
    · rintro _ ⟨x, hx, rfl⟩; exact hlub.1 hx
    · intro u hu
      have : b ≤ ⟨u ⊓ a, inf_le_right⟩ := hlub.2 (fun x hx =>
        show x.val ≤ u ⊓ a from le_inf (hu ⟨x, hx, rfl⟩) x.2)
      exact (show b.val ≤ u ⊓ a from this).trans inf_le_left
  have hd : DirectedOn (· ≤ ·) (Subtype.val '' s) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hxz, hyz⟩ := hdir x hx y hy
    exact ⟨z.val, ⟨z, hz, rfl⟩, hxz, hyz⟩
  have h := hcont _ _ (hsne.image _) hd hl
  rw [Set.image_image] at h
  exact h

theorem g67c_extend {A : Type u} [CompleteBooleanAlgebra A] (a : A) (mu : Set.Iic a → ℝ≥0)
    (hmu : IsPositiveContinuousValuation mu) :
    IsPositiveContinuousValuation (fun x : A => mu ⟨x ⊓ a, inf_le_right⟩) := by
  obtain ⟨⟨hbot, hmod⟩, hmono, hcont⟩ := hmu
  refine ⟨⟨?_, fun x y => ?_⟩, fun x y hxy => hmono (show x ⊓ a ≤ y ⊓ a from inf_le_inf_right a hxy), ?_⟩
  · have : (⟨(⊥ : A) ⊓ a, inf_le_right⟩ : Set.Iic a) = ⊥ := Subtype.ext (by simp)
    simp only; rw [this, hbot]
  · have h1 : (⟨(x ⊔ y) ⊓ a, inf_le_right⟩ : Set.Iic a) =
        (⟨x ⊓ a, inf_le_right⟩ : Set.Iic a) ⊔ ⟨y ⊓ a, inf_le_right⟩ :=
      Subtype.ext (by
        show (x ⊔ y) ⊓ a = (x ⊓ a) ⊔ (y ⊓ a)
        rw [inf_sup_right])
    have h2 : (⟨(x ⊓ y) ⊓ a, inf_le_right⟩ : Set.Iic a) =
        (⟨x ⊓ a, inf_le_right⟩ : Set.Iic a) ⊓ ⟨y ⊓ a, inf_le_right⟩ :=
      Subtype.ext (by
        show (x ⊓ y) ⊓ a = (x ⊓ a) ⊓ (y ⊓ a)
        rw [inf_inf_distrib_right])
    simp only; rw [h1, h2]; exact hmod _ _
  · intro s b hsne hdir hlub
    let g : A → Set.Iic a := fun x => ⟨x ⊓ a, inf_le_right⟩
    have hb : b = sSup s := hlub.unique (isLUB_sSup s)
    have hl : IsLUB (g '' s) (g b) := by
      constructor
      · rintro _ ⟨x, hx, rfl⟩
        exact show x ⊓ a ≤ b ⊓ a from inf_le_inf_right a (hlub.1 hx)
      · intro u hu
        show b ⊓ a ≤ u.val
        rw [hb, sSup_inf_eq]
        exact iSup₂_le fun x hx => (show g x ≤ u from hu ⟨x, hx, rfl⟩)
    have hd : DirectedOn (· ≤ ·) (g '' s) := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hxz, hyz⟩ := hdir x hx y hy
      exact ⟨g z, ⟨z, hz, rfl⟩, show x ⊓ a ≤ z ⊓ a from inf_le_inf_right a hxz,
        show y ⊓ a ≤ z ⊓ a from inf_le_inf_right a hyz⟩
    have h := hcont _ _ (hsne.image _) hd hl
    rw [Set.image_image] at h
    exact h

theorem localizableCriterion (A : Type u) [CompleteBooleanAlgebra A] :
    HasFiniteValuationCover A ↔ ∀ b : A, b ≠ ⊥ →
      ∃ nu : A → ℝ≥0, IsPositiveContinuousValuation nu ∧ nu b ≠ 0 := by
  constructor
  · intro hcov b hb
    have : ∃ g ∈ {a : A | ∃ nu : Set.Iic a → ℝ≥0,
        IsPositiveContinuousValuation nu ∧ ∀ b, nu b = 0 → b = ⊥}, b ⊓ g ≠ ⊥ := by
      by_contra hall
      push Not at hall
      apply hb
      have : b = b ⊓ ⊤ := (inf_top_eq b).symm
      rw [this, ← hcov, inf_sSup_eq]
      exact le_antisymm (iSup₂_le fun d hd => (hall d hd).le) bot_le
    obtain ⟨g, ⟨mu, hmu, hfaith⟩, hbg⟩ := this
    refine ⟨_, g67c_extend g mu hmu, fun h0 => hbg ?_⟩
    have := hfaith _ h0
    exact congrArg Subtype.val this
  · intro h
    unfold HasFiniteValuationCover
    set G := {a : A | ∃ nu : Set.Iic a → ℝ≥0,
        IsPositiveContinuousValuation nu ∧ ∀ b, nu b = 0 → b = ⊥}
    set g := sSup G
    by_contra hne
    have hgc : gᶜ ≠ ⊥ := fun h' => hne (compl_eq_bot.1 h')
    obtain ⟨nu, hnu, hnz⟩ := h gᶜ hgc
    have hnu' := hnu
    obtain ⟨⟨hbot, hmod⟩, hmono, hcont⟩ := hnu'
    let Z : Set A := {x | nu x = 0}
    set n := sSup Z
    have hsupz : ∀ x y, x ∈ Z → y ∈ Z → x ⊔ y ∈ Z := by
      intro x y hx hy
      have := hmod x y
      simp only [Z, Set.mem_setOf_eq] at hx hy ⊢
      rw [hx, hy, zero_add] at this
      exact (add_eq_zero.1 this.symm).1
    have hn : nu n = 0 := by
      have hc := hcont Z n ⟨⊥, hbot⟩
        (fun x hx y hy => ⟨x ⊔ y, hsupz x y hx hy, le_sup_left, le_sup_right⟩) (isLUB_sSup Z)
      exact le_antisymm (hc.2 (by rintro _ ⟨x, hx, rfl⟩; exact le_of_eq hx)) bot_le
    set c := gᶜ ⊓ nᶜ
    have hcG : c ∈ G := by
      refine ⟨fun x => nu x.val, g67c_restrict nu hnu c, fun x hx => ?_⟩
      apply Subtype.ext
      have hxn : x.val ≤ n := le_sSup hx
      have hxc : x.val ≤ nᶜ := x.2.trans inf_le_right
      show x.val = ⊥
      exact le_antisymm (le_inf hxn hxc |>.trans (inf_compl_self n).le) bot_le
    have hcle : c ≤ g := le_sSup hcG
    have hc0 : c = ⊥ := le_antisymm ((le_inf hcle inf_le_left).trans (inf_compl_self g).le) bot_le
    apply hnz
    have h1 : gᶜ ≤ c ⊔ n := by
      rw [sup_comm, sup_inf_left, sup_compl_eq_top, inf_top_eq]; exact le_sup_right
    have h2 := hmono h1
    rw [hc0, bot_sup_eq, hn] at h2
    exact le_antisymm h2 bot_le

end Gelfand273Criterion
end Gelfand320WholeSource22

/- Source module Work.Gelfand320.StepNorming; SHA256 ad9cc61696cd080cd98cc6edb22b4314cca94eb1ff9305de0c5030a776e87d9b. -/
section Gelfand320WholeSource23

set_option autoImplicit false
namespace Gelfand320
open Set TopologicalSpace GelfandVNA.Duality QAlgorithms.Papers.Independent.Support21.P20
open scoped Topology ComplexOrder
noncomputable section
universe u
variable {B : Type u} [CompleteBooleanAlgebra B]

/-- Localizability provides a unit positive valuation concentrated on any
nonempty Boolean part. -/
theorem exists_step_state_on (hB : HasFiniteValuationCover B) (b : B) (hb : b ≠ ⊥) :
    ∃ ψ : StepPredual B, StepPositive ψ ∧ stepBand ψ b = ψ ∧
      ψ.val 1 = 1 ∧ ‖ψ‖ ≤ 1 := by
  obtain ⟨ν, hν, hνb⟩ := (Gelfand273Criterion.localizableCriterion B).1 hB b hb
  obtain ⟨φ, hφ, _, _⟩ := exists_positive_step_functional B (fun p => (ν p : ℝ))
    (nnreal_valuation_continuous ν hν) (fun p => (ν p).coe_nonneg)
  have hφpos : StepPositive φ := by
    intro p
    rw [hφ]
    positivity
  let c : ℝ := (ν b : ℝ)⁻¹
  have hνbpos : 0 < (ν b : ℝ) := by exact_mod_cast pos_iff_ne_zero.mpr hνb
  have hc : 0 < c := inv_pos.mpr hνbpos
  let ψ : StepPredual B := c • stepBand φ b
  have hψ : StepPositive ψ := by
    intro p
    change 0 ≤ c • (stepBand φ b).val (stepProjection B p)
    exact smul_nonneg hc.le (stepBand_positive φ hφpos b p)
  have hψp (p : B) : ψ.val (stepProjection B p) =
      ((c * (ν (p ⊓ b) : ℝ) : ℝ) : ℂ) := by
    change c • (stepBand φ b).val (stepProjection B p) = _
    rw [stepBand_projection, hφ]
    simp only [Complex.real_smul, Complex.ofReal_mul]
  refine ⟨ψ, hψ, ?_, ?_, ?_⟩
  · apply stepPredual_ext
    intro p
    rw [stepBand_projection, hψp, hψp, inf_assoc, inf_idem]
  · rw [← stepProjection_top (B := B), hψp, top_inf_eq]
    simp only [c, inv_mul_cancel₀ (ne_of_gt hνbpos), Complex.ofReal_one]
  · apply (stepPositive_norm_le ψ hψ).trans_eq
    rw [hψp, top_inf_eq, Complex.ofReal_re]
    exact inv_mul_cancel₀ (ne_of_gt hνbpos)

/-- Localizable valuations norm the Stone step algebra. -/
theorem stepEvaluation_norm (hB : HasFiniteValuationCover B) (a : StepAlgebra B) :
    ‖stepEvaluation B a‖ = ‖a‖ := by
  apply le_antisymm
  · apply (stepEvaluation B a).opNorm_le_bound (norm_nonneg a)
    intro φ
    change ‖φ.val a‖ ≤ ‖a‖ * ‖φ.val‖
    simpa only [mul_comm] using φ.val.le_opNorm a
  · apply (ContinuousMap.norm_le a (norm_nonneg _)).2
    intro x
    apply le_of_forall_pos_le_add
    intro ε hε
    letI := booleanSpectrum_totallySeparated B
    have hn : {y | ‖a y - a x‖ < ε} ∈ 𝓝 x := by
      have hc : Continuous (fun y => ‖a y - a x‖) := by fun_prop
      exact (isOpen_lt hc continuous_const).mem_nhds (by simpa using hε)
    obtain ⟨U, hU, hxU, hUa⟩ := isTopologicalBasis_isClopen.mem_nhds_iff.mp hn
    let V : Clopens (PrimeSpectrum (AsBoolRing B)) := ⟨U, hU⟩
    let b : B := (Gelfand272Spectrum.clopensIso B).symm V
    have hb : b ≠ ⊥ := by
      intro hb
      have he : V = ⊥ := by
        rw [← (Gelfand272Spectrum.clopensIso B).apply_symm_apply V]
        change (Gelfand272Spectrum.clopensIso B) b = ⊥
        rw [hb, map_bot]
      have hx : x ∈ V := hxU
      rw [he] at hx
      exact hx
    obtain ⟨ψ, hψpos, hψband, hψone, hψnorm⟩ := exists_step_state_on hB b hb
    have hbval : stepProjection B b = clopenIndicator V := by
      change (clopenProjection ((Gelfand272Spectrum.clopensIso B) b)).val = _
      rw [(Gelfand272Spectrum.clopensIso B).apply_symm_apply]
      rfl
    have hprod : ‖(a - a x • (1 : StepAlgebra B)) * stepProjection B b‖ ≤ ε := by
      apply (ContinuousMap.norm_le _ hε.le).2
      intro y
      rw [hbval]
      by_cases hy : y ∈ U
      · simpa [clopenIndicator, V, hy] using (hUa hy).le
      · simp [clopenIndicator, V, hy, hε.le]
    have he : ψ.val a - a x = ψ.val ((a - a x • (1 : StepAlgebra B)) * stepProjection B b) := by
      rw [← stepBand_apply, hψband, map_sub, map_smul, hψone, smul_eq_mul, mul_one]
    have hd : ‖ψ.val a - a x‖ ≤ ε := by
      rw [he]
      calc
        _ ≤ ‖ψ.val‖ * ‖(a - a x • (1 : StepAlgebra B)) * stepProjection B b‖ := ψ.val.le_opNorm _
        _ ≤ 1 * ε := mul_le_mul hψnorm hprod (norm_nonneg _) zero_le_one
        _ = ε := one_mul ε
    calc
      ‖a x‖ ≤ ‖ψ.val a‖ + ‖ψ.val a - a x‖ := by
        have hh := norm_sub_le (ψ.val a) (ψ.val a - a x)
        simpa only [sub_sub_cancel] using hh
      _ ≤ ‖stepEvaluation B a‖ + ε := add_le_add
        ((stepEvaluation B a).le_opNorm ψ |>.trans (by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hψnorm (norm_nonneg _))) hd

def stepEvaluationIsometry (hB : HasFiniteValuationCover B) :
    StepAlgebra B →ₗᵢ[ℂ] (StepPredual B →L[ℂ] ℂ) where
  toLinearMap := (stepEvaluation B).toLinearMap
  norm_map' := stepEvaluation_norm hB

end
end Gelfand320
end Gelfand320WholeSource23

/- Source module Work.Gelfand320.DualSurjectivity; SHA256 5f053b197bde9cfa398451c627b12cc1fbc28c98b0715231b39b23e6daff6e68. -/
section Gelfand320WholeSource24

set_option autoImplicit false
noncomputable section
namespace Gelfand320
open Set GelfandVNA.Duality QAlgorithms.Papers.Independent.Support21.P20
open scoped ComplexOrder
universe u
variable {B : Type u} [CompleteBooleanAlgebra B]

/-- Uniform approximation of real functionals gives operator-norm approximation
of complex functionals, using the four positive Jordan pieces. -/
theorem exists_step_dual_approximation
    (F : StepPredual B →L[ℂ] ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ a : StepAlgebra B, ‖F - stepEvaluation B a‖ < ε := by
  let δ : ℝ := ε / 16
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let R : StepPredual B →L[ℝ] ℝ := Complex.reCLM.comp (F.restrictScalars ℝ)
  let S : StepPredual B →L[ℝ] ℝ := Complex.imCLM.comp (F.restrictScalars ℝ)
  obtain ⟨a, ha⟩ := exists_real_dual_step R δ hδ
  obtain ⟨b, hb⟩ := exists_real_dual_step S δ hδ
  refine ⟨a + Complex.I • b, ?_⟩
  have hbound : ‖F - stepEvaluation B (a + Complex.I • b)‖ ≤ 4 * (2 * δ) := by
    apply step_dual_norm_bound _ _ (by positivity)
    intro φ hφ
    obtain ⟨haR, haI⟩ := ha φ hφ
    obtain ⟨hbR, hbI⟩ := hb φ hφ
    have hre : (F φ - φ.val (a + Complex.I • b)).re = (F φ).re - (φ.val a).re := by
      simp [map_add, map_smul, smul_eq_mul, Complex.mul_re, hbI]
    have him : (F φ - φ.val (a + Complex.I • b)).im = (F φ).im - (φ.val b).re := by
      simp [map_add, map_smul, smul_eq_mul, Complex.mul_im, haI]
    change ‖F φ - φ.val (a + Complex.I • b)‖ ≤ _
    calc
      _ ≤ |(F φ - φ.val (a + Complex.I • b)).re| +
          |(F φ - φ.val (a + Complex.I • b)).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ δ * stepValuation φ ⊤ + δ * stepValuation φ ⊤ := by
        rw [hre, him]
        exact add_le_add haR hbR
      _ = (2 * δ) * stepValuation φ ⊤ := by ring
  apply lt_of_le_of_lt hbound
  dsimp [δ]
  linarith

/-- The isometric evaluation map has closed, dense range and hence is onto. -/
theorem stepEvaluation_surjective (hB : HasFiniteValuationCover B) :
    Function.Surjective (stepEvaluation B) := by
  let J := stepEvaluationIsometry hB
  have hclosed : IsClosed (Set.range J) :=
    J.isometry.isUniformInducing.isComplete_range.isClosed
  intro F
  have hmem : F ∈ closure (Set.range J) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨a, ha⟩ := exists_step_dual_approximation F ε hε
    refine ⟨J a, ⟨a, rfl⟩, ?_⟩
    rw [dist_eq_norm]
    change ‖F - stepEvaluation B a‖ < ε
    exact ha
  rw [hclosed.closure_eq] at hmem
  exact hmem

/-- The Stone algebra of a localizable complete Boolean algebra has the
candidate space of continuous valuations as a Banach predual. -/
def stepWStarAlgebra (hB : HasFiniteValuationCover B) : WStarAlgebra (StepAlgebra B) where
  exists_predual := by
    let e : StepAlgebra B ≃ₗᵢ[ℂ] (StepPredual B →L[ℂ] ℂ) :=
      LinearIsometryEquiv.ofSurjective (stepEvaluationIsometry hB)
        (stepEvaluation_surjective hB)
    exact ⟨StepPredual B, inferInstance, inferInstance, inferInstance,
      ⟨e.symm.trans (starₗᵢ ℂ)⟩⟩

end Gelfand320
end
end Gelfand320WholeSource24

/- Source module Work.Gelfand39TruncationExtension; SHA256 7cf68e8829232d29be5be85ad60d5401537153c4ca57b9ad2f4e361d1f219ef0. -/
section Gelfand320WholeSource25

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GelfandVNA.Duality Gelfand39OrderContinuity

namespace Gelfand39Truncation
universe u
variable {A : Type u} [CommCStarAlgebra A] [WStarAlgebra A]

def bandRestriction (q : ProjAlg A) (Φ : A →L[ℂ] ℂ) : A →L[ℂ] ℂ where
  toFun a := Φ (q.val * a)
  map_add' := by intro a b; rw [mul_add, map_add]
  map_smul' := by intro c a; rw [mul_smul_comm, map_smul]; rfl
  cont := by fun_prop

theorem band_valuation_add (ν : ProjAlg A → ℝ)
    (hadd : ∀ p r, Disjoint p r → ν (p ⊔ r) = ν p + ν r)
    (q p r : ProjAlg A) (hpr : Disjoint p r) :
    ν (q ⊓ (p ⊔ r)) = ν (q ⊓ p) + ν (q ⊓ r) := by
  rw [inf_sup_left]
  exact hadd _ _ (hpr.mono inf_le_right inf_le_right)

theorem band_restriction_projection (ν : ProjAlg A → ℝ)
    (Φ : A →L[ℂ] ℂ) (hΦ : ∀ p : ProjAlg A, Φ p.val = (ν p : ℂ))
    (q p : ProjAlg A) :
    bandRestriction q Φ p.val = (ν (q ⊓ p) : ℂ) := by
  change Φ (q ⊓ p).val = _
  exact hΦ _

/-- Removing a projection band has norm at most the valuation of its complement. -/
theorem band_tail_bound (ν : ProjAlg A → ℝ) (hzero : ν ⊥ = 0)
    (hadd : ∀ p r, Disjoint p r → ν (p ⊔ r) = ν p + ν r)
    (hpos : ∀ p, 0 ≤ ν p)
    (Φ : A →L[ℂ] ℂ) (hΦ : ∀ p : ProjAlg A, Φ p.val = (ν p : ℂ))
    (q : ProjAlg A) (a : A) :
    ‖Φ a - bandRestriction q Φ a‖ ≤ ν qᶜ * ‖a‖ := by
  have hdiff : Φ a - bandRestriction q Φ a = bandRestriction qᶜ Φ a := by
    change Φ a - Φ (q.val * a) = Φ ((1 - q.val) * a)
    rw [sub_mul, one_mul, map_sub]
  rw [hdiff]
  have h := extension_norm_bound (fun p => ν (qᶜ ⊓ p))
    (by simpa using hzero) (band_valuation_add ν hadd qᶜ) (fun p => hpos _)
    (bandRestriction qᶜ Φ) (band_restriction_projection ν Φ hΦ qᶜ) a
  simpa only [inf_top_eq] using h

end Gelfand39Truncation
end
end Gelfand320WholeSource25

/- Source module Work.Gelfand39DominatedGNS; SHA256 58a863f92e902d0f519969b9ebb05af082ffb112cec545193f4df7436c9369b7. -/
section Gelfand320WholeSource26

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped InnerProductSpace ComplexOrder
open UniformSpace

namespace Gelfand39GNS
universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A functional bounded for the positive functional's GNS seminorm is represented
by a vector in its actual Hilbert completion. -/
theorem exists_gns_vector (μ : A →ₚ[ℂ] ℂ) (Φ : A →ₗ[ℂ] ℂ) (C : ℝ)
    (hbound : ∀ a : A, ‖Φ a‖ ≤ C * ‖μ.toPreGNS a‖) :
    ∃ ξ : μ.GNS, ∀ a : A,
      Φ a = ⟪ξ, (μ.toPreGNS a : μ.GNS)⟫_ℂ := by
  let f : μ.PreGNS →L[ℂ] ℂ :=
    (Φ.comp μ.ofPreGNS.toLinearMap).mkContinuous C (fun a => by
      simpa using hbound (μ.ofPreGNS a))
  refine ⟨(InnerProductSpace.toDual ℂ μ.GNS).symm f.fromCompletion, ?_⟩
  intro a
  rw [InnerProductSpace.toDual_symm_apply,
    ContinuousLinearMap.fromCompletion_apply_coe]
  rfl

/-- GNS vectors can be approximated uniformly on the algebra's norm unit ball by
the multiplication functionals coming from algebra elements. -/
theorem exists_multiplication_approximation (μ : A →ₚ[ℂ] ℂ)
    (Φ : A →ₗ[ℂ] ℂ) (ξ : μ.GNS)
    (hξ : ∀ a : A, Φ a = ⟪ξ, (μ.toPreGNS a : μ.GNS)⟫_ℂ)
    (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ a : A, ‖μ.toPreGNS a‖ ≤ K * ‖a‖)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ b : A, ∀ a : A, ‖Φ a - μ (star b * a)‖ ≤ ε * ‖a‖ := by
  let δ : ℝ := ε / (K + 1)
  have hK1 : 0 < K + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hK1
  obtain ⟨b, hb⟩ :=
    Completion.denseRange_coe.exists_dist_lt ξ hδ
  refine ⟨μ.ofPreGNS b, ?_⟩
  intro a
  have hb' : ‖ξ - (b : μ.GNS)‖ ≤ δ := by
    simpa only [dist_eq_norm] using hb.le
  have hδK : δ * K ≤ ε := by
    calc
      δ * K ≤ δ * (K + 1) := mul_le_mul_of_nonneg_left (by linarith) hδ.le
      _ = ε := div_mul_cancel₀ ε (ne_of_gt hK1)
  calc
    ‖Φ a - μ (star (μ.ofPreGNS b) * a)‖ =
        ‖⟪ξ - (b : μ.GNS), (μ.toPreGNS a : μ.GNS)⟫_ℂ‖ := by
      rw [hξ, inner_sub_left, Completion.inner_coe]
      rw [PositiveLinearMap.preGNS_inner_def]
      simp
    _ ≤ ‖ξ - (b : μ.GNS)‖ * ‖(μ.toPreGNS a : μ.GNS)‖ := norm_inner_le_norm _ _
    _ ≤ δ * (K * ‖a‖) := by
      apply mul_le_mul hb'
      · simpa only [Completion.norm_coe] using hbound a
      · positivity
      · exact hδ.le
    _ = (δ * K) * ‖a‖ := (mul_assoc _ _ _).symm
    _ ≤ ε * ‖a‖ := mul_le_mul_of_nonneg_right hδK (norm_nonneg a)

end Gelfand39GNS
end
end Gelfand320WholeSource26

/- Source module Work.Gelfand39DominatedBounds; SHA256 4f4eec22f2799af4961d5dcddf600db31314a48c3fdeeb610c61c650e986d05c. -/
section Gelfand320WholeSource27

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped InnerProductSpace ComplexOrder

namespace Gelfand39GNS
universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem preGNS_norm_sq_re (μ : A →ₚ[ℂ] ℂ) (a : A) :
    ‖μ.toPreGNS a‖ ^ 2 = (μ (star a * a)).re := by
  simpa only [← Complex.ofReal_pow, Complex.ofReal_re,
    PositiveLinearMap.ofPreGNS_toPreGNS] using
    congrArg Complex.re (μ.preGNS_norm_sq (μ.toPreGNS a))

/-- The GNS seminorm is bounded by the original C*-norm, with an explicit
constant obtained from positivity at the identity. -/
theorem preGNS_norm_le (μ : A →ₚ[ℂ] ℂ) (a : A) :
    ‖μ.toPreGNS a‖ ≤ Real.sqrt ‖μ 1‖ * ‖a‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (norm_nonneg _), preGNS_norm_sq_re]
  calc
    (μ (star a * a)).re ≤ ‖μ (star a * a)‖ := Complex.re_le_norm _
    _ ≤ ‖μ 1‖ * ‖star a * a‖ := μ.norm_apply_le_of_nonneg _ (star_mul_self_nonneg a)
    _ = ‖μ 1‖ * ‖a‖ ^ 2 := by rw [CStarRing.norm_star_mul_self, pow_two]

/-- Positive domination on squares controls the dominated functional in the
dominating functional's GNS seminorm. -/
theorem norm_le_preGNS_of_domination (μ ν : A →ₚ[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hdom : ∀ a : A, (ν (star a * a)).re ≤ C * (μ (star a * a)).re)
    (a : A) :
    ‖ν a‖ ≤ (‖ν.toPreGNS 1‖ * Real.sqrt C) * ‖μ.toPreGNS a‖ := by
  have hnorm : ‖ν.toPreGNS a‖ ≤ Real.sqrt C * ‖μ.toPreGNS a‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt hC, preGNS_norm_sq_re, preGNS_norm_sq_re]
    exact hdom a
  have heq : ν a = ⟪ν.toPreGNS 1, ν.toPreGNS a⟫_ℂ := by
    rw [PositiveLinearMap.preGNS_inner_def]
    simp
  calc
    ‖ν a‖ = ‖⟪ν.toPreGNS 1, ν.toPreGNS a⟫_ℂ‖ := congrArg norm heq
    _ ≤ ‖ν.toPreGNS 1‖ * ‖ν.toPreGNS a‖ := norm_inner_le_norm _ _
    _ ≤ ‖ν.toPreGNS 1‖ * (Real.sqrt C * ‖μ.toPreGNS a‖) :=
      mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
    _ = _ := (mul_assoc _ _ _).symm

end Gelfand39GNS
end
end Gelfand320WholeSource27

/- Source module Work.Gelfand39PredualCriterion; SHA256 05b6f7f916c0ca77e18daa404a2ad0bf9e795500c07873ecf127209d542a37a6. -/
section Gelfand320WholeSource28

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set

namespace Gelfand39Predual
universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Finite-coordinate control on the norm unit ball forces a bounded bidual
functional to be evaluation at an actual element of the given predual. -/
theorem eval_of_finite_kernel_control (Φ : StrongDual ℂ (StrongDual ℂ X))
    (hΦ : ∀ ε : ℝ, 0 < ε → ∃ s : Finset X,
      ∀ f : StrongDual ℂ X, ‖f‖ ≤ 1 → (∀ x ∈ s, f x = 0) → ‖Φ f‖ ≤ ε) :
    ∃ x : X, ∀ f : StrongDual ℂ X, Φ f = f x := by
  classical
  let J : X →ₗᵢ[ℂ] StrongDual ℂ (StrongDual ℂ X) :=
    NormedSpace.inclusionInDoubleDualLi (E := X) ℂ
  let M : Submodule ℂ (StrongDual ℂ (StrongDual ℂ X)) := J.toLinearMap.range
  have hiso : Isometry (fun x : X => J x) := J.isometry
  have hcomplete : IsComplete (Set.range (fun x : X => J x)) :=
    hiso.isUniformInducing.isComplete_range
  have hclosed : IsClosed (Set.range (fun x : X => J x)) := hcomplete.isClosed
  have hmem : Φ ∈ closure (Set.range (fun x : X => J x)) := by
    refine (Metric.mem_closure_iff (a := Φ) (s := Set.range (fun x : X => J x))).2 ?_
    intro ε hε
    obtain ⟨s, hs⟩ := hΦ (ε / 2) (half_pos hε)
    let L : s → StrongDual ℂ X →ₗ[ℂ] ℂ := fun x => (J x.val).toLinearMap
    let N : Submodule ℂ (StrongDual ℂ X) := ⨅ x : s, (L x).ker
    letI : NormedAddCommGroup N := inferInstance
    letI : NormedSpace ℂ N := inferInstance
    let r : StrongDual ℂ N := Φ.comp N.subtypeL
    have hr : ‖r‖ ≤ ε / 2 := by
      apply ContinuousLinearMap.opNorm_le_of_unit_norm (half_pos hε).le
      intro f hf
      apply hs f.val (by change ‖f‖ ≤ 1; rw [hf])
      intro x hx
      have hfx := ((Submodule.mem_iInf (fun y : s => (L y).ker)).mp f.property) ⟨x, hx⟩
      exact hfx
    obtain ⟨g, hg, hgnorm⟩ := exists_extension_norm_eq N r
    let m : StrongDual ℂ (StrongDual ℂ X) := Φ - g
    have hker : (⨅ x : s, (L x).ker) ≤ m.toLinearMap.ker := by
      intro f hf
      change Φ f - g f = 0
      have h := hg (⟨f, hf⟩ : N)
      exact sub_eq_zero.mpr h.symm
    have hm : m.toLinearMap ∈ Submodule.span ℂ (Set.range L) :=
      mem_span_of_iInf_ker_le_ker hker
    have hspan : Submodule.span ℂ (Set.range L) ≤
        M.map (ContinuousLinearMap.coeLM ℂ) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨x, rfl⟩
      exact Submodule.mem_map.mpr ⟨J x.val, ⟨x.val, rfl⟩, rfl⟩
    obtain ⟨m', hm', heq⟩ := Submodule.mem_map.mp (hspan hm)
    have he : m' = m := by
      ext f
      exact LinearMap.congr_fun heq f
    have hmM : m ∈ M := he ▸ hm'
    obtain ⟨x, hx⟩ : ∃ x : X, J x = m := hmM
    refine ⟨m, ⟨x, hx⟩, ?_⟩
    have hdist : dist Φ m ≤ ε / 2 := by
      have hd : dist Φ m = ‖Φ - m‖ := dist_eq_norm Φ m
      rw [hd]
      change ‖Φ - (Φ - g)‖ ≤ ε / 2
      calc
        ‖Φ - (Φ - g)‖ = ‖g‖ :=
          congrArg (fun h : StrongDual ℂ (StrongDual ℂ X) => ‖h‖) (sub_sub_cancel Φ g)
        _ = ‖r‖ := hgnorm
        _ ≤ ε / 2 := hr
    exact hdist.trans_lt (half_lt_self hε)
  rw [hclosed.closure_eq] at hmem
  obtain ⟨x, hx⟩ := hmem
  refine ⟨x, ?_⟩
  intro f
  have h := congrArg (fun ψ : StrongDual ℂ (StrongDual ℂ X) => ψ f) hx
  exact h.symm

end Gelfand39Predual
end
end Gelfand320WholeSource28

/- Source module Work.Gelfand39PredualClosed; SHA256 7dd059d822e4540ded77e03a6d9c7eb2c37e54bb7959fa5a40edd3378461c040. -/
section Gelfand320WholeSource29

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GelfandVNA.Duality

namespace Gelfand39Predual
universe u
variable {A X : Type u} [CStarAlgebra A]
variable [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Uniform norm approximation by vectors from one fixed predual stays in that
same predual. The witnesses are not allowed to vary their ambient predual. -/
theorem exists_predual_vector_of_norm_approximation
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (Φ : A →L[ℂ] ℂ)
    (hΦ : ∀ ε : ℝ, 0 < ε → ∃ x : X,
      ∀ a : A, ‖Φ a - star ((e.symm a) x)‖ ≤ ε * ‖a‖) :
    ∃ x : X, ∀ a : A, Φ a = star ((e.symm a) x) := by
  classical
  let ψ : StrongDual ℂ X →L[ℂ] ℂ := {
    toFun := fun f => star (Φ (e f))
    map_add' := by intro f g; simp
    map_smul' := by
      intro c f
      change star (Φ (e (c • f))) = c • star (Φ (e f))
      rw [e.map_smulₛₗ, Φ.map_smul]
      simp
    cont := (Φ.continuous.comp e.continuous).star }
  obtain ⟨x, hx⟩ := eval_of_finite_kernel_control ψ (by
    intro ε hε
    obtain ⟨x, hx⟩ := hΦ ε hε
    refine ⟨{x}, ?_⟩
    intro f hf hfzero
    have hfx : f x = 0 := hfzero x (Finset.mem_singleton_self x)
    have h := hx (e f)
    simp only [e.symm_apply_apply, hfx, star_zero, sub_zero, e.norm_map] at h
    change ‖star (Φ (e f))‖ ≤ ε
    rw [norm_star]
    exact h.trans ((mul_le_mul_of_nonneg_left hf hε.le).trans_eq (mul_one ε)))
  refine ⟨x, ?_⟩
  intro a
  have h := hx (e.symm a)
  change star (Φ (e (e.symm a))) = (e.symm a) x at h
  rw [e.apply_symm_apply] at h
  rw [← h, star_star]

end Gelfand39Predual
end
end Gelfand320WholeSource29

/- Source module Work.Gelfand39DominatedNormal; SHA256 481a71f3786343060a4aedfaf93dd5e5eaa7a2541c61158784ba7930f8d43e3c. -/
section Gelfand320WholeSource30

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped ComplexOrder
open GelfandVNA.Duality

namespace Gelfand39GNS
universe u
variable {A X : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Positive domination preserves membership in the supplied predual once the
dominating functional's multiplication functionals belong to that predual. -/
theorem exists_predual_vector_of_positive_domination
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (μ ν : A →ₚ[ℂ] ℂ)
    (hμ : ∀ b : A, ∃ x : X, ∀ a : A,
      μ (star b * a) = star ((e.symm a) x))
    (C : ℝ) (hC : 0 ≤ C)
    (hdom : ∀ a : A, (ν (star a * a)).re ≤ C * (μ (star a * a)).re) :
    ∃ x : X, ∀ a : A, ν a = star ((e.symm a) x) := by
  let νc : A →L[ℂ] ℂ := {
    toLinearMap := ν.toLinearMap
    cont := map_continuous ν }
  obtain ⟨ξ, hξ⟩ := exists_gns_vector μ (ν : A →ₗ[ℂ] ℂ)
    (‖ν.toPreGNS 1‖ * Real.sqrt C)
    (norm_le_preGNS_of_domination μ ν C hC hdom)
  apply Gelfand39Predual.exists_predual_vector_of_norm_approximation e νc
  intro ε hε
  obtain ⟨b, hb⟩ := exists_multiplication_approximation μ (ν : A →ₗ[ℂ] ℂ)
    ξ hξ (Real.sqrt ‖μ 1‖) (Real.sqrt_nonneg _) (preGNS_norm_le μ) ε hε
  obtain ⟨x, hx⟩ := hμ b
  refine ⟨x, ?_⟩
  intro a
  rw [← hx a]
  exact hb a

theorem normal_of_positive_domination
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (μ ν : A →ₚ[ℂ] ℂ)
    (hμ : ∀ b : A, ∃ x : X, ∀ a : A,
      μ (star b * a) = star ((e.symm a) x))
    (C : ℝ) (hC : 0 ≤ C)
    (hdom : ∀ a : A, (ν (star a * a)).re ≤ C * (μ (star a * a)).re) :
    IsNormalFunctional ν := by
  obtain ⟨x, hx⟩ := exists_predual_vector_of_positive_domination e μ ν hμ C hC hdom
  exact ⟨X, inferInstance, inferInstance, inferInstance, e, x, hx⟩

end Gelfand39GNS
end
end Gelfand320WholeSource30

/- Source module Work.Gelfand39TruncationDomination; SHA256 1a9680f0731e0c0bc6f048a06bd40944bb00cf307545977c6c4833e1ea8a2798. -/
section Gelfand320WholeSource31

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GelfandVNA.Duality Gelfand39OrderContinuity
open scoped ComplexOrder

namespace Gelfand39Truncation
universe u
variable {A X : Type u} [CommCStarAlgebra A] [WStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A]
variable [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

local instance : LE (ProjAlg A) :=
  (inferInstance : BooleanAlgebra (ProjAlg A)).toPartialOrder.toLE
local instance : Preorder (ProjAlg A) :=
  (inferInstance : BooleanAlgebra (ProjAlg A)).toPartialOrder.toPreorder
local instance : PartialOrder (ProjAlg A) :=
  (inferInstance : BooleanAlgebra (ProjAlg A)).toPartialOrder

theorem band_le_of_projection_bound (μ ν : ProjAlg A → ℝ)
    (hμzero : μ ⊥ = 0)
    (hμadd : ∀ p r, Disjoint p r → μ (p ⊔ r) = μ p + μ r)
    (hμmono : Monotone μ)
    (hνzero : ν ⊥ = 0)
    (hνadd : ∀ p r, Disjoint p r → ν (p ⊔ r) = ν p + ν r)
    (Φ Ψ : A →L[ℂ] ℂ)
    (hΦ : ∀ p : ProjAlg A, Φ p.val = (μ p : ℂ))
    (hΨ : ∀ p : ProjAlg A, Ψ p.val = (ν p : ℂ))
    (q : ProjAlg A) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ p, p ≤ q → ν p ≤ C * μ p)
    {a : A} (ha : 0 ≤ a) :
    bandRestriction q Ψ a ≤ (C : ℂ) * Φ a := by
  let d : ProjAlg A → ℝ := fun p => C * μ p - ν (q ⊓ p)
  let D : A →L[ℂ] ℂ := (C : ℂ) • Φ - bandRestriction q Ψ
  have hd0 : d ⊥ = 0 := by simp [d, hμzero, hνzero]
  have hdadd : ∀ p r, Disjoint p r → d (p ⊔ r) = d p + d r := by
    intro p r hpr
    dsimp [d]
    rw [hμadd p r hpr, band_valuation_add ν hνadd q p r hpr]
    ring
  have hdpos (p : ProjAlg A) : 0 ≤ d p := by
    have h₁ := hbound (q ⊓ p) inf_le_left
    have h₂ := mul_le_mul_of_nonneg_left (hμmono (show q ⊓ p ≤ p from inf_le_right)) hC
    dsimp [d]
    linarith
  have hD (p : ProjAlg A) : D p.val = (d p : ℂ) := by
    change (C : ℂ) * Φ p.val - bandRestriction q Ψ p.val = (d p : ℂ)
    rw [hΦ, band_restriction_projection ν Ψ hΨ]
    dsimp [d]
    push_cast
    rfl
  have h := extension_nonneg d hd0 hdadd hdpos D hD ha
  change 0 ≤ (C : ℂ) * Φ a - bandRestriction q Ψ a at h
  exact sub_nonneg.mp h

/-- Domination on projections of a band makes its positive extension belong to
the given fixed predual. -/
theorem band_exists_predual_vector (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (μ ν : ProjAlg A → ℝ)
    (hμzero : μ ⊥ = 0)
    (hμadd : ∀ p r, Disjoint p r → μ (p ⊔ r) = μ p + μ r)
    (hμpos : ∀ p, 0 ≤ μ p) (hμmono : Monotone μ)
    (hνzero : ν ⊥ = 0)
    (hνadd : ∀ p r, Disjoint p r → ν (p ⊔ r) = ν p + ν r)
    (hνpos : ∀ p, 0 ≤ ν p)
    (Φ Ψ : A →L[ℂ] ℂ)
    (hΦ : ∀ p : ProjAlg A, Φ p.val = (μ p : ℂ))
    (hΨ : ∀ p : ProjAlg A, Ψ p.val = (ν p : ℂ))
    (hΦmult : ∀ b : A, ∃ x : X, ∀ a : A,
      Φ (star b * a) = star ((e.symm a) x))
    (q : ProjAlg A) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ p, p ≤ q → ν p ≤ C * μ p) :
    ∃ x : X, ∀ a : A, bandRestriction q Ψ a = star ((e.symm a) x) := by
  let μp : A →ₚ[ℂ] ℂ := extensionPositiveLinearMap μ hμzero hμadd hμpos Φ hΦ
  let νp : A →ₚ[ℂ] ℂ := extensionPositiveLinearMap
    (fun p => ν (q ⊓ p)) (by simpa using hνzero)
    (band_valuation_add ν hνadd q) (fun p => hνpos _)
    (bandRestriction q Ψ) (band_restriction_projection ν Ψ hΨ q)
  apply Gelfand39GNS.exists_predual_vector_of_positive_domination e μp νp hΦmult C hC
  intro a
  have h := band_le_of_projection_bound μ ν hμzero hμadd hμmono hνzero hνadd
    Φ Ψ hΦ hΨ q C hC hbound (star_mul_self_nonneg a)
  have hr := (Complex.le_def.mp h).1
  change ((bandRestriction q Ψ) (star a * a)).re ≤ C * (Φ (star a * a)).re
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] using hr

/-- If positive dominated bands leave arbitrarily small valuation tails, the
whole bounded extension is represented in the same fixed predual. -/
theorem exists_predual_vector_of_dominated_bands (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (μ ν : ProjAlg A → ℝ)
    (hμzero : μ ⊥ = 0)
    (hμadd : ∀ p r, Disjoint p r → μ (p ⊔ r) = μ p + μ r)
    (hμpos : ∀ p, 0 ≤ μ p) (hμmono : Monotone μ)
    (hνzero : ν ⊥ = 0)
    (hνadd : ∀ p r, Disjoint p r → ν (p ⊔ r) = ν p + ν r)
    (hνpos : ∀ p, 0 ≤ ν p)
    (Φ Ψ : A →L[ℂ] ℂ)
    (hΦ : ∀ p : ProjAlg A, Φ p.val = (μ p : ℂ))
    (hΨ : ∀ p : ProjAlg A, Ψ p.val = (ν p : ℂ))
    (hΦmult : ∀ b : A, ∃ x : X, ∀ a : A,
      Φ (star b * a) = star ((e.symm a) x))
    (hbands : ∀ ε : ℝ, 0 < ε → ∃ q : ProjAlg A, ∃ C : ℝ,
      0 ≤ C ∧ (∀ p, p ≤ q → ν p ≤ C * μ p) ∧ ν qᶜ ≤ ε) :
    ∃ x : X, ∀ a : A, Ψ a = star ((e.symm a) x) := by
  apply Gelfand39Predual.exists_predual_vector_of_norm_approximation e Ψ
  intro ε hε
  obtain ⟨q, C, hC, hb, htail⟩ := hbands ε hε
  obtain ⟨x, hx⟩ := band_exists_predual_vector e μ ν hμzero hμadd hμpos hμmono
    hνzero hνadd hνpos Φ Ψ hΦ hΨ hΦmult q C hC hb
  refine ⟨x, ?_⟩
  intro a
  rw [← hx a]
  exact (band_tail_bound ν hνzero hνadd hνpos Ψ hΨ q a).trans
    (mul_le_mul_of_nonneg_right htail (norm_nonneg a))

end Gelfand39Truncation
end
end Gelfand320WholeSource31

/- Source module Work.Gelfand39AbsoluteContinuity; SHA256 c11b8ea030b2b4445dd05c86ca40d701e9a1de5f9307dac5fb4ea8b609167588. -/
section Gelfand320WholeSource32

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GelfandVNA.Duality Gelfand39OrderContinuity Gelfand311Jordan
open QAlgorithms.Papers.Independent.Support21.P20
open scoped ComplexOrder

namespace Gelfand39Truncation
universe u
variable {A X : Type u} [CommCStarAlgebra A] [WStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A]
variable [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

local instance : LE (ProjAlg A) :=
  (inferInstance : BooleanAlgebra (ProjAlg A)).toPartialOrder.toLE
local instance : Preorder (ProjAlg A) :=
  (inferInstance : BooleanAlgebra (ProjAlg A)).toPartialOrder.toPreorder
local instance : PartialOrder (ProjAlg A) :=
  (inferInstance : BooleanAlgebra (ProjAlg A)).toPartialOrder

/-- The supplied complete structure retains the canonical Boolean operations. -/
def canonicalProjectionCompleteBooleanAlgebra : CompleteBooleanAlgebra (ProjAlg A) := by
  let sup : Set (ProjAlg A) → ProjAlg A := fun s => (Gelfand38.projections_complete s).choose
  have hsup (s : Set (ProjAlg A)) : IsLUB s (sup s) :=
    (Gelfand38.projections_complete s).choose_spec
  exact {
    (inferInstance : BooleanAlgebra (ProjAlg A)) with
    sSup := sup
    sInf := fun s => sup (lowerBounds s)
    isLUB_sSup := hsup
    isGLB_sInf := fun s => isLUB_lowerBounds.mp (hsup (lowerBounds s)) }

/-- A positive continuous projection valuation absolutely continuous with respect
to a fixed-predual positive functional has its own vector in that same predual. -/
theorem exists_predual_vector_of_absolute_continuity
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (μ ν : ProjAlg A → ℝ)
    (hμ : IsContinuousValuation μ) (hν : IsContinuousValuation ν)
    (hμpos : ∀ p, 0 ≤ μ p) (hνpos : ∀ p, 0 ≤ ν p)
    (Φ Ψ : A →L[ℂ] ℂ)
    (hΦ : ∀ p : ProjAlg A, Φ p.val = (μ p : ℂ))
    (hΨ : ∀ p : ProjAlg A, Ψ p.val = (ν p : ℂ))
    (hΦmult : ∀ b : A, ∃ x : X, ∀ a : A,
      Φ (star b * a) = star ((e.symm a) x))
    (hac : ∀ p, μ p = 0 → ν p = 0) :
    ∃ x : X, ∀ a : A, Ψ a = star ((e.symm a) x) := by
  letI := canonicalProjectionCompleteBooleanAlgebra (A := A)
  have hμmono := Gelfand39ValuationSup.monotone_of_positive μ hμ.1 hμpos
  have hνmono := Gelfand39ValuationSup.monotone_of_positive ν hν.1 hνpos
  have hνsplit (p : ProjAlg A) : ν p + ν pᶜ = ν ⊤ := by
    have h := hν.1.2 p pᶜ
    simpa only [sup_compl_eq_top, inf_compl_eq_bot, hν.1.1, add_zero] using h
  have hHahn (n : ℕ) : HahnJordanConclusions
      (fun p => ν p - ((n : ℝ) + 1) * μ p) := by
    apply (hahnJordan_decomposition (ProjAlg A)).1
    exact Or.inr ⟨fun _ => sup_compl_eq_top,
      Gelfand39ValuationSup.sub_const_mul_continuous μ ν hμ hν _⟩
  apply exists_predual_vector_of_dominated_bands e μ ν hμ.1.1
    (Gelfand39ValuationSup.disjoint_add μ hμ.1) hμpos hμmono hν.1.1
    (Gelfand39ValuationSup.disjoint_add ν hν.1) hνpos Φ Ψ hΦ hΨ hΦmult
  intro ε hε
  obtain ⟨n, hn⟩ := exists_small_carrier_complement μ ν hμpos hμmono hνmono
    hνsplit hac hHahn (Gelfand39ValuationSup.isLUB_image ν hν hνpos) ε hε
  refine ⟨carrier μ ν n, (n : ℝ) + 1, by positivity, ?_, hn.le⟩
  exact carrier_bound μ ν hHahn n

end Gelfand39Truncation
end
end Gelfand320WholeSource32

/- Source module Work.Gelfand39ProjectionBand; SHA256 057120f0cafa2b835cc49dfcc16acdcefca15cd04df4f92729c4f489b943c322. -/
section Gelfand320WholeSource33

set_option autoImplicit false

namespace Gelfand39ProjectionBand

open GelfandVNA.Duality Gelfand38 Gelfand39Inverse WeakDual

noncomputable section

lemma complex_eq_zero_of_norm_translate_bound (z : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (h : ∀ c : ℂ, ‖z + c‖ ≤ max r ‖c‖) : z = 0 := by
  by_contra hz
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  let k : ℝ := (r + 1) / ‖z‖
  have hk : 0 < k := div_pos (by linarith) hn
  have hkn : k * ‖z‖ = r + 1 := div_mul_cancel₀ _ hn.ne'
  have hnorm : ‖k • z‖ = r + 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hk, hkn]
  have heq : z + k • z = (1 + k) • z := by rw [add_smul, one_smul]
  have ht := h (k • z)
  rw [hnorm, max_eq_right (by linarith), heq, norm_smul,
    Real.norm_eq_abs, abs_of_pos (by linarith)] at ht
  nlinarith

variable {A : Type*} [CommCStarAlgebra A]

lemma projection_bandBall_iff (p : ProjAlg A) (r : ℝ) (hr : 0 ≤ r) (a : A) :
    (p.val * a = a ∧ ‖a‖ ≤ r) ↔
      ∀ c : ℂ, ‖a + c • (1 - p.val)‖ ≤ max r ‖c‖ := by
  constructor
  · rintro ⟨hpa, hnorm⟩ c
    rw [← gelfand_norm]
    apply (ContinuousMap.norm_le _ (hr.trans (le_max_left _ _))).mpr
    intro χ
    have hmul := congrArg (fun a : A => gelfandTransform ℂ A a χ) hpa
    simp only [map_mul, ContinuousMap.mul_apply] at hmul
    simp only [map_add, ContinuousMap.add_apply, map_smul, ContinuousMap.smul_apply,
      map_sub, ContinuousMap.sub_apply, map_one, ContinuousMap.one_apply, smul_eq_mul]
    rcases projection_value_zero_or_one p χ with hp | hp
    · have ha0 : gelfandTransform ℂ A a χ = 0 := by simpa only [hp, zero_mul] using hmul.symm
      rw [hp, ha0, sub_zero, mul_one, zero_add]
      exact le_max_right _ _
    · rw [hp, sub_self, mul_zero, add_zero]
      exact (character_norm_le χ a).trans (hnorm.trans (le_max_left _ _))
  · intro h
    have hn : ‖a‖ ≤ r := by
      simpa only [zero_smul, add_zero, norm_zero, max_eq_left hr] using h 0
    refine ⟨?_, hn⟩
    apply (gelfandTransform_isometry A).injective
    ext χ
    simp only [map_mul, ContinuousMap.mul_apply]
    rcases projection_value_zero_or_one p χ with hp | hp
    · have ha0 : gelfandTransform ℂ A a χ = 0 := by
        apply complex_eq_zero_of_norm_translate_bound _ r hr
        intro c
        have hi := (character_norm_le χ (a + c • (1 - p.val))).trans (h c)
        simpa only [map_add, ContinuousMap.add_apply, map_smul, ContinuousMap.smul_apply,
          map_sub, ContinuousMap.sub_apply, map_one, ContinuousMap.one_apply,
          hp, sub_zero, smul_eq_mul, mul_one] using hi
      rw [hp, ha0, mul_zero]
    · rw [hp, one_mul]

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

lemma isClosed_projection_bandBall (p : ProjAlg A) (r : ℝ) (hr : 0 ≤ r)
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) :
    IsClosed {w : WeakDual ℂ X |
      p.val * e (WeakDual.toStrongDual w) = e (WeakDual.toStrongDual w) ∧
        ‖e (WeakDual.toStrongDual w)‖ ≤ r} := by
  simp only [projection_bandBall_iff p r hr, Set.ofPred_forall]
  apply isClosed_iInter
  intro c
  simpa only [sub_neg_eq_add] using
    isClosed_normBall e (-(c • (1 - p.val))) (max r ‖c‖)


end
end Gelfand39ProjectionBand
end Gelfand320WholeSource33

/- Source module Work.Gelfand39ProjectionGraph; SHA256 3e0d48f1c14a21ada87d8a39d6b8f1e4f5a7a520728045b70e9ee3636af707a9. -/
section Gelfand320WholeSource34

set_option autoImplicit false

namespace Gelfand39ProjectionBand

open GelfandVNA.Duality Gelfand38 Gelfand39Inverse WeakDual

noncomputable section

lemma continuous_of_isClosed_graph {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    [CompactSpace T] (f : S → T) (hg : IsClosed {z : S × T | f z.1 = z.2}) : Continuous f := by
  apply continuous_iff_isClosed.mpr
  intro C hC
  have hc := isClosedMap_fst_of_compactSpace
    ({z : S × T | f z.1 = z.2} ∩ Prod.snd ⁻¹' C) (hg.inter (hC.preimage continuous_snd))
  convert hc using 1
  ext x
  constructor
  · intro hx
    exact ⟨(x, f x), ⟨rfl, hx⟩, rfl⟩
  · rintro ⟨⟨y, z⟩, ⟨h, hz⟩, rfl⟩
    change f y ∈ C
    change f y = z at h
    change z ∈ C at hz
    rw [h]
    exact hz

variable {A : Type*} [CommCStarAlgebra A]

lemma projection_mul_norm_le (p : ProjAlg A) (a : A) : ‖p.val * a‖ ≤ ‖a‖ := by
  calc
    _ ≤ ‖p.val‖ * ‖a‖ := norm_mul_le _ _
    _ ≤ 1 * ‖a‖ := mul_le_mul_of_nonneg_right
      (positiveUnit_norm_le (projection_positiveUnit p)) (norm_nonneg a)
    _ = ‖a‖ := one_mul _

lemma projection_graph_band_iff (p : ProjAlg A) (a b : A) (ha : ‖a‖ ≤ 1) :
    p.val * a = b ↔
      (p.val * b = b ∧ ‖b‖ ≤ 1) ∧
      ((pᶜ : ProjAlg A).val * (a - b) = a - b ∧ ‖a - b‖ ≤ 1) := by
  constructor
  · rintro rfl
    have hp : p.val * p.val = p.val := p.isStarProjection.1
    have he : a - p.val * a = (pᶜ : ProjAlg A).val * a := by
      change a - p.val * a = (1 - p.val) * a
      ring
    refine ⟨⟨?_, (projection_mul_norm_le p a).trans ha⟩, ?_⟩
    · rw [← mul_assoc, hp]
    · rw [he]
      constructor
      · rw [← mul_assoc, (pᶜ : ProjAlg A).isStarProjection.1]
      · exact (projection_mul_norm_le pᶜ a).trans ha
  · rintro ⟨⟨hpb, hbn⟩, hcomp, hcn⟩
    change (1 - p.val) * (a - b) = a - b at hcomp
    have hzero : p.val * (a - b) = 0 := by
      rw [sub_mul, one_mul, sub_eq_self] at hcomp
      exact hcomp
    have h := hzero
    rw [mul_sub, hpb, sub_eq_zero] at h
    exact h

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

def weakUnitBall (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X] : Set (WeakDual ℂ X) :=
  {w | ‖WeakDual.toStrongDual w‖ ≤ 1}

lemma isCompact_weakUnitBall : IsCompact (weakUnitBall X) := by
  simpa only [weakUnitBall, Set.preimage, Metric.mem_closedBall, dist_zero_right] using
    (WeakDual.isCompact_closedBall (0 : StrongDual ℂ X) 1)

def projectWeak (p : ProjAlg A) (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (w : WeakDual ℂ X) : WeakDual ℂ X :=
  StrongDual.toWeakDual (e.symm (p.val * e (WeakDual.toStrongDual w)))

lemma projectWeak_mem (p : ProjAlg A) (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    {w : WeakDual ℂ X} (hw : w ∈ weakUnitBall X) : projectWeak p e w ∈ weakUnitBall X := by
  change ‖e.symm (p.val * e (WeakDual.toStrongDual w))‖ ≤ 1
  rw [e.symm.norm_map]
  change ‖WeakDual.toStrongDual w‖ ≤ 1 at hw
  exact (projection_mul_norm_le p _).trans (by simpa only [e.norm_map] using hw)

lemma projectWeak_eq_iff (p : ProjAlg A) (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (w v : WeakDual ℂ X) : projectWeak p e w = v ↔
      p.val * e (WeakDual.toStrongDual w) = e (WeakDual.toStrongDual v) := by
  change (e.symm (p.val * e (WeakDual.toStrongDual w)) = WeakDual.toStrongDual v) ↔ _
  constructor
  · intro h
    simpa only [e.apply_symm_apply] using congrArg e h
  · intro h
    apply e.injective
    simpa only [e.apply_symm_apply] using h

def projectWeakBall (p : ProjAlg A) (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) :
    weakUnitBall X → weakUnitBall X :=
  fun w => ⟨projectWeak p e w.val, projectWeak_mem p e w.property⟩

lemma continuous_projectWeakBall (p : ProjAlg A) (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) :
    Continuous (projectWeakBall p e) := by
  letI : CompactSpace (weakUnitBall X) := isCompact_iff_compactSpace.mp isCompact_weakUnitBall
  apply continuous_of_isClosed_graph
  have hd : IsClosed {z : WeakDual ℂ X × WeakDual ℂ X |
      (pᶜ : ProjAlg A).val * (e (WeakDual.toStrongDual z.1) - e (WeakDual.toStrongDual z.2)) =
        e (WeakDual.toStrongDual z.1) - e (WeakDual.toStrongDual z.2) ∧
      ‖e (WeakDual.toStrongDual z.1) - e (WeakDual.toStrongDual z.2)‖ ≤ 1} := by
    convert (isClosed_projection_bandBall pᶜ 1 zero_le_one e).preimage
      (continuous_fst.sub continuous_snd) using 1
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    change (_ ∧ _) ↔ (_ * e (WeakDual.toStrongDual z.1 - WeakDual.toStrongDual z.2) =
      e (WeakDual.toStrongDual z.1 - WeakDual.toStrongDual z.2) ∧
      ‖e (WeakDual.toStrongDual z.1 - WeakDual.toStrongDual z.2)‖ ≤ 1)
    rw [map_sub]
  have h1 := (isClosed_projection_bandBall p 1 zero_le_one e).preimage
    (continuous_subtype_val.comp (continuous_snd : Continuous (Prod.snd :
      weakUnitBall X × weakUnitBall X → weakUnitBall X)))
  have hc2 : Continuous (fun z : weakUnitBall X × weakUnitBall X => (z.1.val, z.2.val)) := by
    fun_prop
  have h2 := hd.preimage hc2
  convert h1.inter h2 using 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
  rw [Subtype.ext_iff]
  change projectWeak p e z.1.val = z.2.val ↔ _
  rw [projectWeak_eq_iff]
  have hz1 : ‖WeakDual.toStrongDual z.1.val‖ ≤ 1 := z.1.property
  exact projection_graph_band_iff p _ _ (by simpa only [e.norm_map] using hz1)


end
end Gelfand39ProjectionBand
end Gelfand320WholeSource34

/- Source module Work.Gelfand39StarGraph; SHA256 bd9eda9e636f47fb30ccf51eae62f05a93235636ba93460f59f30fb42124bbe3. -/
section Gelfand320WholeSource35

set_option autoImplicit false

namespace Gelfand39ProjectionBand

open GelfandVNA.Duality Gelfand38 Gelfand39Inverse WeakDual

noncomputable section

variable {A : Type*} [CommCStarAlgebra A]

def halfSum (a b : A) : A := (1 / 2 : ℂ) • (a + b)
def imagHalfDiff (a b : A) : A := (Complex.I / 2) • (a - b)

lemma star_graph_unit_iff (a b : A) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    star a = b ↔
      (IsSelfAdjoint (halfSum a b) ∧ ‖halfSum a b‖ ≤ 1) ∧
      (IsSelfAdjoint (imagHalfDiff a b) ∧ ‖imagHalfDiff a b‖ ≤ 1) := by
  have hI : star (Complex.I : ℂ) = -Complex.I := by
    change (starRingEnd ℂ) Complex.I = -Complex.I
    exact Complex.conj_I
  have hnorm1 : ‖halfSum a b‖ ≤ 1 := by
    have h := norm_add_le a b
    dsimp [halfSum]
    rw [norm_smul]
    norm_num [norm_div]
    linarith
  have hnorm2 : ‖imagHalfDiff a b‖ ≤ 1 := by
    have h := norm_sub_le a b
    dsimp [imagHalfDiff]
    rw [norm_smul]
    norm_num [norm_div]
    linarith
  constructor
  · rintro rfl
    refine ⟨⟨?_, hnorm1⟩, ⟨?_, hnorm2⟩⟩
    · change star ((1 / 2 : ℂ) • (a + star a)) = (1 / 2 : ℂ) • (a + star a)
      simp [star_smul, add_comm]
    · change star ((Complex.I / 2) • (a - star a)) = (Complex.I / 2) • (a - star a)
      simp only [star_smul, star_div₀, hI, star_ofNat, star_sub, star_star]
      module
  · rintro ⟨⟨hx, hnx⟩, ⟨hy, hny⟩⟩
    have hi : (Complex.I : ℂ) * (Complex.I / 2) = -(1 / 2 : ℂ) := by
      rw [← mul_div_assoc, Complex.I_mul_I]
      norm_num
    have h1 : halfSum a b - Complex.I • imagHalfDiff a b = a := by
      dsimp [halfSum, imagHalfDiff]
      rw [smul_smul, hi]
      module
    have h2 : halfSum a b + Complex.I • imagHalfDiff a b = b := by
      dsimp [halfSum, imagHalfDiff]
      rw [smul_smul, hi]
      module
    calc
      star a = star (halfSum a b - Complex.I • imagHalfDiff a b) := congrArg star h1.symm
      _ = halfSum a b + Complex.I • imagHalfDiff a b := by
        rw [star_sub, star_smul, hx.star_eq, hy.star_eq, hI]
        module
      _ = b := h2

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

lemma e_conj_smul (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (c : ℂ) (u : StrongDual ℂ X) :
    e (star c • u) = c • e u := by
  rw [e.map_smulₛₗ, starRingEnd_apply, star_star]

lemma isClosed_selfAdjoint_unit (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) :
    IsClosed {w : WeakDual ℂ X |
      IsSelfAdjoint (e (WeakDual.toStrongDual w)) ∧ ‖e (WeakDual.toStrongDual w)‖ ≤ 1} := by
  simp only [selfAdjoint_unit_iff_norm_balls, Set.ofPred_forall]
  apply isClosed_iInter
  intro t
  simpa only [sub_neg_eq_add] using
    isClosed_normBall e (-(((t : ℂ) * Complex.I) • (1 : A))) (Real.sqrt (1 + t ^ 2))

def starWeak (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (w : WeakDual ℂ X) : WeakDual ℂ X :=
  StrongDual.toWeakDual (e.symm (star (e (WeakDual.toStrongDual w))))

lemma starWeak_mem (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    {w : WeakDual ℂ X} (hw : w ∈ weakUnitBall X) : starWeak e w ∈ weakUnitBall X := by
  change ‖e.symm (star (e (WeakDual.toStrongDual w)))‖ ≤ 1
  rw [e.symm.norm_map, norm_star, e.norm_map]
  exact hw

lemma starWeak_eq_iff (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (w v : WeakDual ℂ X) :
    starWeak e w = v ↔ star (e (WeakDual.toStrongDual w)) = e (WeakDual.toStrongDual v) := by
  change (e.symm (star (e (WeakDual.toStrongDual w))) = WeakDual.toStrongDual v) ↔ _
  constructor
  · intro h
    simpa only [e.apply_symm_apply] using congrArg e h
  · intro h
    apply e.injective
    simpa only [e.apply_symm_apply] using h

def starWeakBall (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) : weakUnitBall X → weakUnitBall X :=
  fun w => ⟨starWeak e w.val, starWeak_mem e w.property⟩

lemma continuous_starWeakBall (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) : Continuous (starWeakBall e) := by
  letI : CompactSpace (weakUnitBall X) := isCompact_iff_compactSpace.mp isCompact_weakUnitBall
  apply continuous_of_isClosed_graph
  have h1 : IsClosed {z : weakUnitBall X × weakUnitBall X |
      IsSelfAdjoint (halfSum (e (WeakDual.toStrongDual z.1.val)) (e (WeakDual.toStrongDual z.2.val))) ∧
      ‖halfSum (e (WeakDual.toStrongDual z.1.val)) (e (WeakDual.toStrongDual z.2.val))‖ ≤ 1} := by
    have hc : Continuous (fun z : weakUnitBall X × weakUnitBall X =>
        star (1 / 2 : ℂ) • (z.1.val + z.2.val)) := by fun_prop
    convert (isClosed_selfAdjoint_unit e).preimage hc using 1
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    change (_ ∧ _) ↔ (IsSelfAdjoint (e (star (1 / 2 : ℂ) •
      (WeakDual.toStrongDual z.1.val + WeakDual.toStrongDual z.2.val))) ∧
      ‖e (star (1 / 2 : ℂ) • (WeakDual.toStrongDual z.1.val + WeakDual.toStrongDual z.2.val))‖ ≤ 1)
    simp only [e_conj_smul, map_add, halfSum]
  have h2 : IsClosed {z : weakUnitBall X × weakUnitBall X |
      IsSelfAdjoint (imagHalfDiff (e (WeakDual.toStrongDual z.1.val)) (e (WeakDual.toStrongDual z.2.val))) ∧
      ‖imagHalfDiff (e (WeakDual.toStrongDual z.1.val)) (e (WeakDual.toStrongDual z.2.val))‖ ≤ 1} := by
    have hc : Continuous (fun z : weakUnitBall X × weakUnitBall X =>
        star (Complex.I / 2) • (z.1.val - z.2.val)) := by fun_prop
    convert (isClosed_selfAdjoint_unit e).preimage hc using 1
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    change (_ ∧ _) ↔ (IsSelfAdjoint (e (star (Complex.I / 2) •
      (WeakDual.toStrongDual z.1.val - WeakDual.toStrongDual z.2.val))) ∧
      ‖e (star (Complex.I / 2) • (WeakDual.toStrongDual z.1.val - WeakDual.toStrongDual z.2.val))‖ ≤ 1)
    simp only [e_conj_smul, map_sub, imagHalfDiff]
  convert h1.inter h2 using 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
  rw [Subtype.ext_iff]
  change starWeak e z.1.val = z.2.val ↔ _
  rw [starWeak_eq_iff]
  have hz1 : ‖WeakDual.toStrongDual z.1.val‖ ≤ 1 := z.1.property
  have hz2 : ‖WeakDual.toStrongDual z.2.val‖ ≤ 1 := z.2.property
  exact star_graph_unit_iff _ _ (by simpa only [e.norm_map] using hz1)
    (by simpa only [e.norm_map] using hz2)


end
end Gelfand39ProjectionBand
end Gelfand320WholeSource35

/- Source module Work.Gelfand39ProjectionEvaluation; SHA256 14d005ded358a475c5aaa236352486de11f8e7e92fc554665e16f9cad3274b7a. -/
section Gelfand320WholeSource36

set_option autoImplicit false

namespace Gelfand39ProjectionBand

open GelfandVNA.Duality WeakDual
noncomputable section

variable {A X : Type*} [CommCStarAlgebra A]
variable [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Evaluation at a fixed vector in a supplied predual. -/
def fixedEvaluation (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (x : X) : A →L[ℂ] ℂ where
  toFun a := star ((e.symm a) x)
  map_add' := by intro a b; simp
  map_smul' := by
    intro c a
    rw [e.symm.map_smulₛₗ]
    simp
  cont := by fun_prop

/-- Restrict a fixed predual evaluation to the band of a projection. -/
def projectionEvaluation (p : ProjAlg A) (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (x : X) :
    A →L[ℂ] ℂ where
  toFun a := fixedEvaluation e x (p.val * a)
  map_add' := by intro a b; rw [mul_add, map_add]
  map_smul' := by intro c a; rw [mul_smul_comm, map_smul]; rfl
  cont := by fun_prop

/-- Conjugate a fixed predual evaluation by the algebra adjoint. -/
def adjointEvaluation (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (x : X) : A →L[ℂ] ℂ where
  toFun a := (e.symm (star a)) x
  map_add' := by intro a b; simp
  map_smul' := by
    intro c a
    rw [star_smul, e.symm.map_smulₛₗ]
    simp
  cont := by fun_prop

lemma fixedEvaluation_add_vector (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (x y : X) (a : A) :
    fixedEvaluation e (x + y) a = fixedEvaluation e x a + fixedEvaluation e y a := by
  simp only [fixedEvaluation, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
    AddHom.coe_mk, map_add, star_add]

lemma fixedEvaluation_conj_smul_vector (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (c : ℂ) (x : X) (a : A) :
    fixedEvaluation e (star c • x) a = c • fixedEvaluation e x a := by
  change star ((e.symm a) (star c • x)) = c • star ((e.symm a) x)
  rw [map_smul, star_smul, star_star]

lemma adjointEvaluation_projection (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (x : X) (p : ProjAlg A) :
    adjointEvaluation e x p.val = star (fixedEvaluation e x p.val) := by
  change (e.symm (star p.val)) x = star (star ((e.symm p.val) x))
  rw [p.isStarProjection.2.star_eq, star_star]

lemma continuous_projectionEvaluation_ball (p : ProjAlg A)
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (x : X) :
    Continuous (fun w : weakUnitBall X => projectionEvaluation p e x (e (toStrongDual w.val))) := by
  have hc := ((WeakDual.eval_continuous (𝕜 := ℂ) x).comp continuous_subtype_val).comp
    (continuous_projectWeakBall p e)
  exact hc.star

lemma continuous_adjointEvaluation_ball (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (x : X) :
    Continuous (fun w : weakUnitBall X => adjointEvaluation e x (e (toStrongDual w.val))) := by
  exact ((WeakDual.eval_continuous (𝕜 := ℂ) x).comp continuous_subtype_val).comp
    (continuous_starWeakBall e)


end
end Gelfand39ProjectionBand
end Gelfand320WholeSource36

/- Source module Work.Gelfand39PredualBall; SHA256 27a86e121b8c59b2d1c8bf5a066eac6a25d0d421f1c098f3ddd489efc126345b. -/
section Gelfand320WholeSource37

set_option autoImplicit false
noncomputable section
open Set Filter Topology WeakDual

namespace Gelfand39Predual
universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Weak-star continuity on the closed norm unit ball already forces a
bounded bidual functional to come from the given complete predual. -/
theorem eval_of_weakStarContinuousOn_ball (Φ : StrongDual ℂ (StrongDual ℂ X))
    (hΦ : ContinuousOn (fun w : WeakDual ℂ X => Φ (WeakDual.toStrongDual w))
      (WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ X) 1)) :
    ∃ x : X, ∀ f : StrongDual ℂ X, Φ f = f x := by
  classical
  apply eval_of_finite_kernel_control Φ
  intro ε hε
  let K : Set (WeakDual ℂ X) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ X) 1
  let g : WeakDual ℂ X → ℂ := fun w => Φ (WeakDual.toStrongDual w)
  have hz : (0 : WeakDual ℂ X) ∈ K := by simp [K]
  have hc : ContinuousWithinAt g K 0 := hΦ 0 hz
  have hsmall : {w : WeakDual ℂ X | ‖g w‖ < ε} ∈ nhdsWithin 0 K := by
    have h := hc.preimage_mem_nhdsWithin (Metric.ball_mem_nhds (g 0) hε)
    change {w : WeakDual ℂ X | dist (g w) (g 0) < ε} ∈ nhdsWithin 0 K at h
    simpa only [g, map_zero, dist_zero_right] using h
  obtain ⟨U, hU, hUK⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hsmall
  obtain ⟨⟨s, r⟩, hr, hsub⟩ :=
    ((topDualPairing ℂ X).weakBilin_withSeminorms.hasBasis_zero_ball).mem_iff.mp hU
  refine ⟨s, ?_⟩
  intro f hf hzero
  have hfU : StrongDual.toWeakDual f ∈ U := by
    apply hsub
    rw [Seminorm.ball_zero_eq]
    apply Seminorm.finset_sup_apply_lt hr
    intro x hx
    change ‖f x‖ < r
    rw [hzero x hx, norm_zero]
    exact hr
  have hfK : StrongDual.toWeakDual f ∈ K := by
    change dist f (0 : StrongDual ℂ X) ≤ 1
    simpa only [dist_zero_right] using hf
  exact (hUK ⟨hfU, hfK⟩).le

end Gelfand39Predual
end
end Gelfand320WholeSource37

/- Source module Work.Gelfand39NormalOnBall; SHA256 bcfdc1f3030b7f477cf51e833e246847856c39af5aee1e7352fd45a26645bac3. -/
section Gelfand320WholeSource38

set_option autoImplicit false
noncomputable section
open WeakDual GelfandVNA.Duality

namespace Gelfand39Predual
universe u
variable {A X : Type u} [CStarAlgebra A]
variable [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The unit-ball criterion keeps the witness in the supplied fixed predual. -/
theorem exists_predual_vector_of_weakStarContinuousOn_ball
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (Φ : A →L[ℂ] ℂ)
    (hΦ : ContinuousOn (fun w : WeakDual ℂ X => Φ (e (WeakDual.toStrongDual w)))
      (WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ X) 1)) :
    ∃ x : X, ∀ a : A, Φ a = star ((e.symm a) x) := by
  let ψ : StrongDual ℂ X →L[ℂ] ℂ := {
    toFun := fun f => star (Φ (e f))
    map_add' := by
      intro f g
      simp
    map_smul' := by
      intro c f
      change star (Φ (e (c • f))) = c • star (Φ (e f))
      rw [e.map_smulₛₗ, Φ.map_smul]
      simp
    cont := (Φ.continuous.comp e.continuous).star }
  have hc : ContinuousOn (fun w : WeakDual ℂ X => ψ (WeakDual.toStrongDual w))
      (WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ X) 1) := hΦ.star
  obtain ⟨x, hx⟩ := eval_of_weakStarContinuousOn_ball ψ hc
  refine ⟨x, ?_⟩
  intro a
  have h := hx (e.symm a)
  change star (Φ (e (e.symm a))) = (e.symm a) x at h
  rw [e.apply_symm_apply] at h
  rw [← h, star_star]

/-- Continuity on the fixed predual's closed norm unit ball suffices for the
exact canonical normal-functional predicate. -/
theorem normal_of_weakStarContinuousOn_ball (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (Φ : A →L[ℂ] ℂ)
    (hΦ : ContinuousOn (fun w : WeakDual ℂ X => Φ (e (WeakDual.toStrongDual w)))
      (WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ X) 1)) :
    IsNormalFunctional Φ := by
  obtain ⟨x, hx⟩ := exists_predual_vector_of_weakStarContinuousOn_ball e Φ hΦ
  exact ⟨X, inferInstance, inferInstance, inferInstance, e, x, hx⟩

end Gelfand39Predual
end
end Gelfand320WholeSource38

/- Source module Work.Gelfand39NormalActions; SHA256 ae7ca5c5341e9a57e1fee4dbe382a54c0bce5daaf4cbfb4e662a251a59fa5fb0. -/
section Gelfand320WholeSource39

set_option autoImplicit false

namespace Gelfand39ProjectionBand

open GelfandVNA.Duality WeakDual Gelfand39Predual
noncomputable section
universe u

variable {A X : Type u} [CommCStarAlgebra A]
variable [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma weakUnitBall_eq : weakUnitBall X =
    WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ X) 1 := by
  ext w
  simp only [weakUnitBall, Set.mem_ofPred_eq, Set.mem_preimage,
    Metric.mem_closedBall, dist_zero_right]

/-- The projection-band action preserves the original supplied predual. -/
theorem exists_projection_vector (p : ProjAlg A)
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (x : X) :
    ∃ y : X, ∀ a, projectionEvaluation p e x a = fixedEvaluation e y a := by
  apply exists_predual_vector_of_weakStarContinuousOn_ball e (projectionEvaluation p e x)
  rw [← weakUnitBall_eq]
  exact continuousOn_iff_continuous_restrict.mpr (continuous_projectionEvaluation_ball p e x)

/-- Adjoint-conjugation of functionals preserves the original supplied predual. -/
theorem exists_adjoint_vector (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (x : X) :
    ∃ y : X, ∀ a, adjointEvaluation e x a = fixedEvaluation e y a := by
  apply exists_predual_vector_of_weakStarContinuousOn_ball e (adjointEvaluation e x)
  rw [← weakUnitBall_eq]
  exact continuousOn_iff_continuous_restrict.mpr (continuous_adjointEvaluation_ball e x)

theorem normal_projection (p : ProjAlg A) (φ : A → ℂ) (hφ : IsNormalFunctional φ) :
    IsNormalFunctional (fun a => φ (p.val * a)) := by
  obtain ⟨Y, hY, hN, hC, e, x, hx⟩ := hφ
  obtain ⟨y, hy⟩ := exists_projection_vector p e x
  refine ⟨Y, inferInstance, inferInstance, inferInstance, e, y, ?_⟩
  intro a
  change φ (p.val * a) = star ((e.symm a) y)
  rw [hx]
  exact hy a

theorem normal_adjoint (φ : A → ℂ) (hφ : IsNormalFunctional φ) :
    IsNormalFunctional (fun a => star (φ (star a))) := by
  obtain ⟨Y, hY, hN, hC, e, x, hx⟩ := hφ
  obtain ⟨y, hy⟩ := exists_adjoint_vector e x
  refine ⟨Y, inferInstance, inferInstance, inferInstance, e, y, ?_⟩
  intro a
  change star (φ (star a)) = star ((e.symm a) y)
  rw [hx, star_star]
  exact hy a


end
end Gelfand39ProjectionBand
end Gelfand320WholeSource39

/- Source module Work.Gelfand39Hermitian; SHA256 1a122da1318b360ce98c3d858e419838a11df86751a8e3a3a2b10d926b8f2119. -/
section Gelfand320WholeSource40

set_option autoImplicit false

namespace Gelfand39ProjectionBand
open GelfandVNA.Duality WeakDual Gelfand39Predual
noncomputable section
universe u
variable {A X : Type u} [CommCStarAlgebra A]
variable [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def realEvaluation (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (x : X) : A →L[ℂ] ℂ :=
  (1 / 2 : ℂ) • (fixedEvaluation e x + adjointEvaluation e x)

def imagEvaluation (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (x : X) : A →L[ℂ] ℂ :=
  (-Complex.I / 2) • (fixedEvaluation e x - adjointEvaluation e x)

lemma realEvaluation_projection (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (x : X) (p : ProjAlg A) :
    realEvaluation e x p.val = ((fixedEvaluation e x p.val).re : ℂ) := by
  change (1 / 2 : ℂ) * (fixedEvaluation e x p.val + adjointEvaluation e x p.val) = _
  rw [adjointEvaluation_projection]
  change (1 / 2 : ℂ) * (fixedEvaluation e x p.val +
    (starRingEnd ℂ) (fixedEvaluation e x p.val)) = _
  rw [Complex.add_conj, Complex.ofReal_mul]
  norm_num <;> ring

lemma imagEvaluation_projection (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (x : X) (p : ProjAlg A) :
    imagEvaluation e x p.val = ((fixedEvaluation e x p.val).im : ℂ) := by
  change (-Complex.I / 2) * (fixedEvaluation e x p.val - adjointEvaluation e x p.val) = _
  rw [adjointEvaluation_projection]
  change (-Complex.I / 2) * (fixedEvaluation e x p.val -
    (starRingEnd ℂ) (fixedEvaluation e x p.val)) = _
  rw [Complex.sub_conj, Complex.ofReal_mul, Complex.ofReal_ofNat]
  have hI := Complex.I_mul_I
  linear_combination -((fixedEvaluation e x p.val).im : ℂ) * hI

lemma continuous_fixedEvaluation_ball (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (x : X) :
    Continuous (fun w : weakUnitBall X => fixedEvaluation e x (e (toStrongDual w.val))) := by
  have hc := ((WeakDual.eval_continuous (𝕜 := ℂ) x).comp
    (continuous_subtype_val : Continuous (Subtype.val : weakUnitBall X → WeakDual ℂ X))).star
  simpa only [fixedEvaluation, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
    AddHom.coe_mk, e.symm_apply_apply, WeakDual.toStrongDual_apply, Function.comp_def] using hc

lemma exists_real_vector (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (x : X) :
    ∃ y : X, ∀ a, realEvaluation e x a = fixedEvaluation e y a := by
  apply exists_predual_vector_of_weakStarContinuousOn_ball e (realEvaluation e x)
  rw [← weakUnitBall_eq]
  apply continuousOn_iff_continuous_restrict.mpr
  exact (continuous_fixedEvaluation_ball e x |>.add
    (continuous_adjointEvaluation_ball e x)).const_smul (1 / 2 : ℂ)

lemma exists_imag_vector (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (x : X) :
    ∃ y : X, ∀ a, imagEvaluation e x a = fixedEvaluation e y a := by
  apply exists_predual_vector_of_weakStarContinuousOn_ball e (imagEvaluation e x)
  rw [← weakUnitBall_eq]
  apply continuousOn_iff_continuous_restrict.mpr
  exact (continuous_fixedEvaluation_ball e x |>.sub
    (continuous_adjointEvaluation_ball e x)).const_smul (-Complex.I / 2)

end
end Gelfand39ProjectionBand
end Gelfand320WholeSource40

/- Source module Work.Gelfand39ForwardCore; SHA256 9b85295d30d57f362080c9c0a173ac0bd1b569b27f36e5a3aad0209088077339. -/
section Gelfand320WholeSource41

set_option autoImplicit false

namespace Gelfand39

open Gelfand38 GelfandVNA.Duality WeakDual Set Filter
open QAlgorithms.Papers.Independent.Support21.P20
open scoped Topology

variable {A : Type*} [CommCStarAlgebra A]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

lemma projection_isLUB_positive (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (s : Set (ProjAlg A)) (hs : s.Nonempty) (hd : DirectedOn (· ≤ ·) s)
    (a : ProjAlg A) (ha : IsLUB s a) :
    ∀ b : A, PositiveUnit b → (∀ p ∈ s, SpectralLE p.val b) → SpectralLE a.val b := by
  classical
  let : Nonempty s := hs.to_subtype
  have hdir : Directed SpectralLE (fun p : s => p.val.val) := by
    intro p q
    obtain ⟨r, hr, hpr, hqr⟩ := hd p.val p.property q.val q.property
    exact ⟨⟨r, hr⟩, (projection_le_iff _ _).1 hpr, (projection_le_iff _ _).1 hqr⟩
  obtain ⟨c, hc, hub, hleast⟩ := exists_positive_lub e (fun p : s => p.val.val)
    (fun p => projection_positiveUnit p.val) hdir
  have hcc : c * c = c := spectralLE_antisymm (positiveUnit_square hc) hc
    (positiveUnit_square_le hc)
    (hleast (c * c) (positiveUnit_square hc) (fun p => projection_le_square p.val hc (hub p)))
  let q : ProjAlg A := ⟨⟨c, hcc⟩, (gelfand_selfAdjoint_iff c).2 (fun χ => (hc χ).1)⟩
  have hq : IsLUB s q := by
    constructor
    · intro p hp
      exact (projection_le_iff p q).2 (hub ⟨p, hp⟩)
    · intro p hp
      exact (projection_le_iff q p).2
        (hleast p.val (projection_positiveUnit p)
          (fun r => (projection_le_iff r.val p).1 (hp r.property)))
  have hqa : q = a := hq.unique ha
  intro b hb hub'
  rw [← hqa]
  exact hleast b hb (fun p => hub' p.val p.property)

theorem projections_tendsto_predual (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (s : Set (ProjAlg A)) (hs : s.Nonempty) (hd : DirectedOn (· ≤ ·) s)
    (a : ProjAlg A) (ha : IsLUB s a) :
    Tendsto (fun p : s => StrongDual.toWeakDual (e.symm p.val.val)) atTop
      (𝓝 (StrongDual.toWeakDual (e.symm a.val))) := by
  classical
  let : Nonempty s := hs.to_subtype
  let : IsDirectedOrder s := hd.isDirectedOrder
  let lift : A → WeakDual ℂ X := fun a => StrongDual.toWeakDual (e.symm a)
  let eval : WeakDual ℂ X → A := fun w => e (WeakDual.toStrongDual w)
  have hlift (b : A) : eval (lift b) = b := e.apply_symm_apply b
  change Tendsto (fun p : s => lift p.val.val) atTop (𝓝 (lift a.val))
  apply (isCompact_positiveUnit e).tendsto_nhds_of_unique_mapClusterPt
  · exact Eventually.of_forall (fun p => by
      change PositiveUnit (eval (lift p.val.val))
      rw [hlift]
      exact projection_positiveUnit p.val)
  · intro w hw hcluster
    have hupper : ∀ p ∈ s, SpectralLE p.val (eval w) := by
      intro p hp
      have hc := (isClosed_positiveUnit_lower e p.val (projection_positiveUnit p)).mem_of_mapClusterPt
        hcluster
      apply (hc ?_).2
      filter_upwards [eventually_ge_atTop (⟨p, hp⟩ : s)] with q hq
      change PositiveUnit (eval (lift q.val.val)) ∧ SpectralLE p.val (eval (lift q.val.val))
      rw [hlift]
      exact ⟨projection_positiveUnit q.val, (projection_le_iff p q.val).1 hq⟩
    have hbelow : SpectralLE (eval w) a.val := by
      have hc := (isClosed_positiveUnit_upper e a.val (projection_positiveUnit a)).mem_of_mapClusterPt
        hcluster
      apply (hc ?_).2
      apply Eventually.of_forall
      intro p
      change PositiveUnit (eval (lift p.val.val)) ∧ SpectralLE (eval (lift p.val.val)) a.val
      rw [hlift]
      exact ⟨projection_positiveUnit p.val, (projection_le_iff p.val a).1 (ha.1 p.property)⟩
    have habove := projection_isLUB_positive e s hs hd a ha (eval w) hw hupper
    have heq : eval w = a.val := spectralLE_antisymm hw (projection_positiveUnit a) hbelow habove
    apply WeakDual.toStrongDual.injective
    apply e.injective
    change eval w = eval (lift a.val)
    rw [hlift]
    exact heq

theorem normal_restrict_isContinuousValuation (φ : A → ℂ) (hφ : IsNormalFunctional φ) :
    IsContinuousValuation (fun p : ProjAlg A => φ p.val) := by
  obtain ⟨X, hX, hN, hC, e, x, hφ⟩ := hφ
  have hzero : φ 0 = 0 := by simp [hφ]
  have hadd (a b : A) : φ (a + b) = φ a + φ b := by simp [hφ]
  constructor
  · constructor
    · exact hzero
    · intro p q
      rw [← hadd, ← hadd]
      apply congrArg φ
      change p.val + q.val = (p.val + q.val - p.val * q.val) + p.val * q.val
      abel
  · intro s a hs hd ha
    have hc : Continuous (fun w : WeakDual ℂ X => star (w x)) :=
      (WeakDual.eval_continuous x).star
    have ht := hc.continuousAt.tendsto.comp (projections_tendsto_predual e s hs hd a ha)
    simpa only [Function.comp_def, hφ, StrongDual.toWeakDual_apply] using ht


end Gelfand39
end Gelfand320WholeSource41

/- Source module Work.Gelfand39NormalJordan; SHA256 c1588cf21d510abd79835cbe8dc6f1d59f8df5ae9b5149f67bb4041baf61d94d. -/
section Gelfand320WholeSource42

set_option autoImplicit false

namespace Gelfand39NormalJordan
open GelfandVNA.Duality Gelfand38 Gelfand39 Gelfand39Inverse Gelfand39ProjectionBand
open Gelfand39OrderContinuity Gelfand311Jordan
open QAlgorithms.Papers.Independent.Support21.P20
open scoped ComplexOrder
noncomputable section
universe u
variable {A X : Type u} [CommCStarAlgebra A] [WStarAlgebra A]
variable [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def projectionCompleteBooleanAlgebra (A : Type u) [CommCStarAlgebra A]
    [WStarAlgebra A] : CompleteBooleanAlgebra (ProjAlg A) := by
  let sup : Set (ProjAlg A) → ProjAlg A := fun s => (projections_complete s).choose
  have hsup (s : Set (ProjAlg A)) : IsLUB s (sup s) := (projections_complete s).choose_spec
  exact {
    (inferInstance : BooleanAlgebra (ProjAlg A)) with
    sSup := sup
    sInf := fun s => sup (lowerBounds s)
    isLUB_sSup := hsup
    isGLB_sInf := fun s => isLUB_lowerBounds.mp (hsup (lowerBounds s)) }

/-- Real-on-projections fixed-predual functionals have a positive Jordan
split whose two representing vectors remain in that same predual. -/
theorem real_jordan_vectors (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (x : X)
    (hx : ∀ p : ProjAlg A, (fixedEvaluation e x p.val).im = 0) :
    letI := CStarAlgebra.spectralOrder A
    ∃ y z : X,
      (∀ a : A, 0 ≤ a → 0 ≤ fixedEvaluation e y a) ∧
      (∀ a : A, 0 ≤ a → 0 ≤ fixedEvaluation e z a) ∧
      ∀ a : A, fixedEvaluation e x a = fixedEvaluation e y a - fixedEvaluation e z a := by
  letI := CStarAlgebra.spectralOrder A
  letI := CStarAlgebra.spectralOrderedRing A
  letI := projectionCompleteBooleanAlgebra A
  let ν : ProjAlg A → ℝ := fun p => (fixedEvaluation e x p.val).re
  have hreal (p : ProjAlg A) : fixedEvaluation e x p.val = (ν p : ℂ) := by
    apply Complex.ext
    · rfl
    · exact hx p
  have hn : IsNormalFunctional (fixedEvaluation e x) :=
    ⟨X, inferInstance, inferInstance, inferInstance, e, x, fun _ => rfl⟩
  have hc := normal_restrict_isContinuousValuation (fixedEvaluation e x) hn
  have hν : IsContinuousValuation ν := g72gk34_cmap Complex.re Complex.zero_re
    Complex.add_re Complex.continuous_re hc
  have hj := (hahnJordan_decomposition (ProjAlg A)).1 ν
    (Or.inr ⟨fun _ => sup_compl_eq_top, hν⟩)
  rcases hj with ⟨_, _, _, _, hpn, hmn, hp, hm, hsplit⟩
  obtain ⟨y, hy⟩ := exists_projection_vector (positiveCarrier ν) e x
  obtain ⟨w, hw⟩ := exists_projection_vector (negativeCarrier ν) e x
  have hneg (a : A) : fixedEvaluation e (-w) a = -fixedEvaluation e w a := by
    change star ((e.symm a) (-w)) = -star ((e.symm a) w)
    rw [map_neg, star_neg]
  have hyproj (p : ProjAlg A) : fixedEvaluation e y p.val = (jordanPositive ν p : ℂ) := by
    rw [← hy p.val]
    change fixedEvaluation e x (positiveCarrier ν ⊓ p).val = _
    exact hreal _
  have hzproj (p : ProjAlg A) : fixedEvaluation e (-w) p.val = (jordanNegative ν p : ℂ) := by
    rw [hneg, ← hw p.val]
    change -fixedEvaluation e x (negativeCarrier ν ⊓ p).val = _
    rw [hreal]
    exact (Complex.ofReal_neg _).symm
  refine ⟨y, -w, ?_, ?_, ?_⟩
  · intro a ha
    exact extension_nonneg (jordanPositive ν) hpn.1.1.1
      (fun p q hd => g72gk34_disj hpn hd.eq_bot) hp (fixedEvaluation e y) hyproj ha
  · intro a ha
    exact extension_nonneg (jordanNegative ν) hmn.1.1.1
      (fun p q hd => g72gk34_disj hmn hd.eq_bot) hm (fixedEvaluation e (-w)) hzproj ha
  · have he : fixedEvaluation e x = fixedEvaluation e y - fixedEvaluation e (-w) := by
      apply ContinuousLinearMap.ext_on (projection_span_dense A)
      rintro a ⟨p, rfl⟩
      change fixedEvaluation e x p.val = fixedEvaluation e y p.val - fixedEvaluation e (-w) p.val
      rw [hreal, hyproj, hzproj]
      exact_mod_cast hsplit p
    intro a
    exact congrArg (fun F : A →L[ℂ] ℂ => F a) he

/-- Every evaluation in a fixed predual splits into four positive evaluations
in that same predual, with the usual real/imaginary Jordan identity. -/
theorem complex_jordan_vectors (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (x : X) :
    letI := CStarAlgebra.spectralOrder A
    ∃ y₁ y₂ y₃ y₄ : X,
      (∀ a : A, 0 ≤ a → 0 ≤ fixedEvaluation e y₁ a) ∧
      (∀ a : A, 0 ≤ a → 0 ≤ fixedEvaluation e y₂ a) ∧
      (∀ a : A, 0 ≤ a → 0 ≤ fixedEvaluation e y₃ a) ∧
      (∀ a : A, 0 ≤ a → 0 ≤ fixedEvaluation e y₄ a) ∧
      ∀ a : A, fixedEvaluation e x a = fixedEvaluation e y₁ a - fixedEvaluation e y₂ a +
        Complex.I * (fixedEvaluation e y₃ a - fixedEvaluation e y₄ a) := by
  letI := CStarAlgebra.spectralOrder A
  obtain ⟨xr, hxr⟩ := exists_real_vector e x
  obtain ⟨xi, hxi⟩ := exists_imag_vector e x
  have hr (p : ProjAlg A) : (fixedEvaluation e xr p.val).im = 0 := by
    rw [← hxr, realEvaluation_projection]
    rfl
  have hi (p : ProjAlg A) : (fixedEvaluation e xi p.val).im = 0 := by
    rw [← hxi, imagEvaluation_projection]
    rfl
  obtain ⟨y₁, y₂, hy₁, hy₂, hyr⟩ := real_jordan_vectors e xr hr
  obtain ⟨y₃, y₄, hy₃, hy₄, hyi⟩ := real_jordan_vectors e xi hi
  refine ⟨y₁, y₂, y₃, y₄, hy₁, hy₂, hy₃, hy₄, ?_⟩
  have he : fixedEvaluation e x = realEvaluation e x + Complex.I • imagEvaluation e x := by
    apply ContinuousLinearMap.ext_on (projection_span_dense A)
    rintro a ⟨p, rfl⟩
    change fixedEvaluation e x p.val = realEvaluation e x p.val + Complex.I * imagEvaluation e x p.val
    rw [realEvaluation_projection, imagEvaluation_projection]
    simpa only [mul_comm] using (Complex.re_add_im (fixedEvaluation e x p.val)).symm
  intro a
  have h := congrArg (fun F : A →L[ℂ] ℂ => F a) he
  change fixedEvaluation e x a = realEvaluation e x a + Complex.I * imagEvaluation e x a at h
  rw [hxr, hxi, hyr, hyi] at h
  exact h

/-- Positive evaluations in any fixed supplied predual detect every nonzero
canonical projection. -/
theorem positive_evaluation_separates_projection (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (p : ProjAlg A) (hp : p ≠ ⊥) :
    letI := CStarAlgebra.spectralOrder A
    ∃ y : X, (∀ a : A, 0 ≤ a → 0 ≤ fixedEvaluation e y a) ∧ fixedEvaluation e y p.val ≠ 0 := by
  classical
  letI := CStarAlgebra.spectralOrder A
  have hex : ∃ x : X, fixedEvaluation e x p.val ≠ 0 := by
    by_contra h
    push Not at h
    have hz : e.symm p.val = 0 := by
      ext x
      exact star_eq_zero.mp (h x)
    have hpv : p.val = 0 := by
      simpa only [e.apply_symm_apply, map_zero] using congrArg e hz
    apply hp
    apply Subtype.ext
    apply Subtype.ext
    exact hpv
  obtain ⟨x, hx⟩ := hex
  obtain ⟨y₁, y₂, y₃, y₄, hy₁, hy₂, hy₃, hy₄, he⟩ := complex_jordan_vectors e x
  by_cases h₁ : fixedEvaluation e y₁ p.val = 0
  · by_cases h₂ : fixedEvaluation e y₂ p.val = 0
    · by_cases h₃ : fixedEvaluation e y₃ p.val = 0
      · refine ⟨y₄, hy₄, ?_⟩
        intro h₄
        apply hx
        rw [he, h₁, h₂, h₃, h₄]
        simp
      · exact ⟨y₃, hy₃, h₃⟩
    · exact ⟨y₂, hy₂, h₂⟩
  · exact ⟨y₁, hy₁, h₁⟩

end
end Gelfand39NormalJordan
end Gelfand320WholeSource42

/- Source module Work.Gelfand39FaithfulCover; SHA256 d453a3cde7bbec4ea85f0e44cb4a42755ea4a4ec62339018de797a3e6cd3e6c9. -/
section Gelfand320WholeSource43

set_option autoImplicit false
noncomputable section
open Set Filter

namespace Gelfand39FaithfulCover
universe u
variable {B : Type u} [CompleteBooleanAlgebra B]

theorem strictMonoOn_of_faithful_on (ν : B → ℝ) (p : B) (hzero : ν ⊥ = 0)
    (hadd : ∀ a b, ν a + ν b = ν (a ⊔ b) + ν (a ⊓ b))
    (hpos : ∀ a, 0 ≤ ν a)
    (hfaithful : ∀ a, a ≤ p → ν a = 0 → a = ⊥) :
    StrictMonoOn ν (Set.Iic p) := by
  intro a ha b hb hab
  let d := b ⊓ aᶜ
  have hdle : d ≤ p := inf_le_left.trans hb
  have hd : d ≠ ⊥ := by
    intro hd
    have hba : b ≤ a := by
      calc
        b = b ⊓ (a ⊔ aᶜ) := by simp
        _ = (b ⊓ a) ⊔ (b ⊓ aᶜ) := inf_sup_left b a aᶜ
        _ = b ⊓ a := by change (b ⊓ a) ⊔ d = b ⊓ a; rw [hd, sup_bot_eq]
        _ ≤ a := inf_le_right
    exact (not_le_of_gt hab) hba
  have hdpos : 0 < ν d := lt_of_le_of_ne (hpos d) (by
    intro h
    exact hd (hfaithful d hdle h.symm))
  have hunion : a ⊔ d = b := by
    dsimp [d]
    rw [sup_inf_left, sup_eq_right.mpr hab.le, sup_compl_eq_top, inf_top_eq]
  have hinter : a ⊓ d = ⊥ := by
    dsimp [d]
    calc
      a ⊓ (b ⊓ aᶜ) = (a ⊓ aᶜ) ⊓ b := by ac_rfl
      _ = ⊥ := by simp
  have h := hadd a d
  rw [hunion, hinter, hzero] at h
  linarith

/-- Countable selection within a faithful principal part needs no Boolean
algebra structure on the subtype interval. -/
theorem exists_sequence_sup_on (ν : B → ℝ) (hmono : Monotone ν) (p : B)
    (hν : StrictMonoOn ν (Set.Iic p))
    (s : Set B) (hs : s.Nonempty) (hsp : s ⊆ Set.Iic p)
    (hSup : IsLUB (ν '' s) (ν (sSup s))) :
    ∃ f : ℕ → B, (∀ n, f n ∈ s) ∧ iSup f = sSup s := by
  classical
  obtain ⟨v, _, _, hvlim, hv⟩ := hSup.exists_seq_monotone_tendsto (hs.image ν)
  choose f hfs hfv using hv
  refine ⟨f, hfs, ?_⟩
  have hf_le : iSup f ≤ sSup s := iSup_le (fun n => le_sSup (hfs n))
  have hs_le : sSup s ≤ p := sSup_le hsp
  have hf_le_p : iSup f ≤ p := hf_le.trans hs_le
  have hval : ν (sSup s) ≤ ν (iSup f) := by
    apply le_of_tendsto hvlim
    apply Eventually.of_forall
    intro n
    rw [← hfv n]
    exact hmono (le_iSup f n)
  by_contra hne
  have hlt : iSup f < sSup s := lt_of_le_of_ne hf_le hne
  exact (not_lt_of_ge hval) (hν hf_le_p hs_le hlt)

end Gelfand39FaithfulCover
end
end Gelfand320WholeSource43

/- Source module Work.Gelfand39PredualSeries; SHA256 bb8196ec6fdaee280a2415a44df12cb3ba82e070b125f331614d440cfe6b0cff. -/
section Gelfand320WholeSource44

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped ComplexOrder

namespace Gelfand39PredualSeries
universe u
variable {A X : Type u} [CStarAlgebra A]
variable [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Evaluation, viewed as a real continuous linear map in the predual vector. -/
def evaluation (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (a : A) : X →L[ℝ] ℂ :=
  (starL' ℝ : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.comp ((e.symm a).restrictScalars ℝ)

@[simp] theorem evaluation_apply (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (a : A) (x : X) :
    evaluation e a x = star ((e.symm a) x) := rfl

/-- A countable family of positive fixed-predual evaluations has one positive
fixed-predual evaluation with exactly their common zero set. -/
theorem exists_positive_sum (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (S : Set A) (x : ℕ → X)
    (hx : ∀ n a, a ∈ S → 0 ≤ evaluation e a (x n)) :
    ∃ y : X, ∀ a ∈ S, 0 ≤ evaluation e a y ∧
      (evaluation e a y = 0 ↔ ∀ n, evaluation e a (x n) = 0) := by
  let w : ℕ → ℝ := fun n => (1 / 2 : ℝ) ^ n / (‖x n‖ + 1)
  have hw (n : ℕ) : 0 < w n := div_pos (by positivity) (by positivity)
  let z : ℕ → X := fun n => w n • x n
  have hz : Summable z := by
    apply Summable.of_norm_bounded
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1))
    intro n
    change ‖w n • x n‖ ≤ (1 / 2 : ℝ) ^ n
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hw n)]
    calc
      w n * ‖x n‖ ≤ w n * (‖x n‖ + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (hw n).le
      _ = (1 / 2 : ℝ) ^ n := div_mul_cancel₀ _ (by positivity)
  refine ⟨∑' n, z n, ?_⟩
  intro a ha
  let E : X →L[ℝ] ℂ := evaluation e a
  have hsum : E (∑' n, z n) = ∑' n, E (z n) := E.map_tsum hz
  have hEsum : Summable (fun n => E (z n)) := E.summable hz
  have hEpos (n : ℕ) : 0 ≤ E (z n) := by
    change 0 ≤ E (w n • x n)
    rw [map_smul]
    exact smul_nonneg (hw n).le (hx n a ha)
  change 0 ≤ E (∑' n, z n) ∧
    (E (∑' n, z n) = 0 ↔ ∀ n, E (x n) = 0)
  rw [hsum]
  refine ⟨tsum_nonneg hEpos, ?_⟩
  constructor
  · intro hzero n
    have hle : E (z n) ≤ ∑' k, E (z k) := by
      simpa using hEsum.sum_le_tsum ({n} : Finset ℕ) (fun k _ => hEpos k)
    have hn : E (z n) = 0 := le_antisymm (hzero ▸ hle) (hEpos n)
    change E (w n • x n) = 0 at hn
    rw [map_smul, smul_eq_zero] at hn
    exact hn.resolve_left (ne_of_gt (hw n))
  · intro hzero
    have hterm (n : ℕ) : E (z n) = 0 := by
      change E (w n • x n) = 0
      rw [map_smul, hzero n, smul_zero]
    simp only [hterm, tsum_zero]

end Gelfand39PredualSeries
end
end Gelfand320WholeSource44

/- Source module Work.Gelfand39NormalMeasure; SHA256 79abc80c3bfee97e34e126ccf0bc436e643706e64f8a945b9d3e9d64ea0762be. -/
section Gelfand320WholeSource45

set_option autoImplicit false

namespace Gelfand39NormalMeasure
open Set Filter GelfandVNA.Duality Gelfand39ProjectionBand Gelfand39NormalJordan
open Gelfand39FaithfulValuation Gelfand39 Gelfand39OrderContinuity Gelfand38
open QAlgorithms.Papers.Independent.Support21.P20
open scoped ComplexOrder Topology
noncomputable section
universe u

section Support
variable {B : Type*} [CompleteBooleanAlgebra B]

def support (ν : B → ℝ) : B := (sSup {b : B | ν b = 0})ᶜ

lemma valuation_monotone (ν : B → ℝ) (hc : IsContinuousValuation ν)
    (hp : ∀ b, 0 ≤ ν b) : Monotone ν := by
  have hn : IsNormalValuation ν := ⟨hc, fun b => by rw [compl_compl]⟩
  intro a b hab
  have h := Gelfand311Jordan.g72gk34_split hn hab
  linarith [hp (b ⊓ aᶜ)]

lemma valuation_sup (ν : B → ℝ) (hc : IsContinuousValuation ν)
    (hp : ∀ b, 0 ≤ ν b) (s : Set B) (hs : s.Nonempty) (hd : DirectedOn (· ≤ ·) s) :
    IsLUB (ν '' s) (ν (sSup s)) := by
  letI : Nonempty s := hs.to_subtype
  letI : IsDirectedOrder s := hd.isDirectedOrder
  have hm := valuation_monotone ν hc hp
  have hl := isLUB_of_tendsto_atTop (fun (p q : s) hpq => hm hpq)
    (hc.2 s (sSup s) hs hd (isLUB_sSup s))
  simpa only [Set.image_eq_range] using hl

lemma null_sup_zero (ν : B → ℝ) (hc : IsContinuousValuation ν)
    (hp : ∀ b, 0 ≤ ν b) : ν (sSup {b : B | ν b = 0}) = 0 :=
  null_sup_null ν hc.1.1 hc.1.2 hp (valuation_sup ν hc hp)

lemma null_iff_disjoint_support (ν : B → ℝ) (hc : IsContinuousValuation ν)
    (hp : ∀ b, 0 ≤ ν b) (b : B) : ν b = 0 ↔ Disjoint b (support ν) := by
  rw [support, disjoint_compl_right_iff]
  exact null_iff_le_null_sup ν hp (valuation_monotone ν hc hp) (null_sup_zero ν hc hp) b

lemma eq_of_same_disjoint (a b : B) (h : ∀ q, Disjoint q a ↔ Disjoint q b) : a = b := by
  have he : aᶜ = bᶜ := le_antisymm
    (((h aᶜ).mp disjoint_compl_left).le_compl_right)
    (((h bᶜ).mpr disjoint_compl_left).le_compl_right)
  simpa only [compl_compl] using congrArg (fun q : B => qᶜ) he

lemma support_sup (ν μ ρ : B → ℝ)
    (hν : IsContinuousValuation ν) (hμ : IsContinuousValuation μ) (hρ : IsContinuousValuation ρ)
    (hpν : ∀ b, 0 ≤ ν b) (hpμ : ∀ b, 0 ≤ μ b) (hpρ : ∀ b, 0 ≤ ρ b)
    (he : ∀ b, ρ b = 0 ↔ ν b = 0 ∧ μ b = 0) : support ρ = support ν ⊔ support μ := by
  apply eq_of_same_disjoint
  intro b
  rw [disjoint_sup_right, ← null_iff_disjoint_support ρ hρ hpρ,
    ← null_iff_disjoint_support ν hν hpν, ← null_iff_disjoint_support μ hμ hpμ]
  exact he b

lemma support_iSup (ν : ℕ → B → ℝ) (μ : B → ℝ)
    (hν : ∀ n, IsContinuousValuation (ν n)) (hμ : IsContinuousValuation μ)
    (hpν : ∀ n b, 0 ≤ ν n b) (hpμ : ∀ b, 0 ≤ μ b)
    (he : ∀ b, μ b = 0 ↔ ∀ n, ν n b = 0) : support μ = ⨆ n, support (ν n) := by
  apply eq_of_same_disjoint
  intro b
  rw [disjoint_iSup_iff, ← null_iff_disjoint_support μ hμ hpμ, he b]
  exact forall_congr' (fun n => null_iff_disjoint_support (ν n) (hν n) (hpν n) b)

end Support

variable {A X : Type u} [CommCStarAlgebra A] [WStarAlgebra A]
variable [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
local instance : CompleteBooleanAlgebra (ProjAlg A) := projectionCompleteBooleanAlgebra A

/-- Positivity of the actual complex-linear evaluation in the canonical C*-order. -/
def Positive (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (x : X) : Prop :=
  letI := CStarAlgebra.spectralOrder A
  ∀ a : A, 0 ≤ a → 0 ≤ fixedEvaluation e x a

def value (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (x : X) (p : ProjAlg A) : ℝ :=
  (fixedEvaluation e x p.val).re

lemma value_continuous (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (x : X) :
    IsContinuousValuation (value e x) := by
  have hn : IsNormalFunctional (fixedEvaluation e x) :=
    ⟨X, inferInstance, inferInstance, inferInstance, e, x, fun _ => rfl⟩
  exact Gelfand311Jordan.g72gk34_cmap Complex.re Complex.zero_re Complex.add_re Complex.continuous_re
    (normal_restrict_isContinuousValuation (fixedEvaluation e x) hn)

lemma evaluation_projection_nonneg (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) {x : X}
    (hx : Positive e x) (p : ProjAlg A) : 0 ≤ fixedEvaluation e x p.val := by
  letI := CStarAlgebra.spectralOrder A
  letI := CStarAlgebra.spectralOrderedRing A
  exact hx p.val ((positiveUnit_iff_mem_Icc p.val).mp (projection_positiveUnit p)).1

lemma value_nonneg (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) {x : X}
    (hx : Positive e x) (p : ProjAlg A) : 0 ≤ value e x p :=
  (Complex.nonneg_iff.mp (evaluation_projection_nonneg e hx p)).1

lemma value_zero_iff (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) {x : X}
    (hx : Positive e x) (p : ProjAlg A) : value e x p = 0 ↔ fixedEvaluation e x p.val = 0 := by
  constructor
  · intro h
    apply Complex.ext h
    exact (Complex.nonneg_iff.mp (evaluation_projection_nonneg e hx p)).2.symm
  · intro h
    exact congrArg Complex.re h

lemma positive_add (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) {x y : X}
    (hx : Positive e x) (hy : Positive e y) : Positive e (x + y) := by
  intro a ha
  rw [fixedEvaluation_add_vector]
  exact add_nonneg (hx a ha) (hy a ha)

lemma support_add (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) {x y : X}
    (hx : Positive e x) (hy : Positive e y) :
    support (value e (x + y)) = support (value e x) ⊔ support (value e y) := by
  apply support_sup _ _ _ (value_continuous e x) (value_continuous e y)
    (value_continuous e (x + y)) (value_nonneg e hx) (value_nonneg e hy)
    (value_nonneg e (positive_add e hx hy))
  intro p
  change (fixedEvaluation e (x + y) p.val).re = 0 ↔ _
  rw [fixedEvaluation_add_vector, Complex.add_re]
  exact add_eq_zero_iff_of_nonneg (value_nonneg e hx p) (value_nonneg e hy p)

lemma exists_positive_projection_vector (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (x : X) (hx : Positive e x) (p : ProjAlg A) :
    ∃ y : X, Positive e y ∧ (∀ a, fixedEvaluation e y a = fixedEvaluation e x (p.val * a)) ∧
      support (value e y) ≤ p := by
  obtain ⟨y, hy⟩ := exists_projection_vector p e x
  have he (a : A) : fixedEvaluation e y a = fixedEvaluation e x (p.val * a) := (hy a).symm
  have hpos : Positive e y := by
    letI := CStarAlgebra.spectralOrder A
    letI := CStarAlgebra.spectralOrderedRing A
    intro a ha
    rw [he]
    apply hx
    exact Commute.mul_nonneg
      ((positiveUnit_iff_mem_Icc p.val).mp (projection_positiveUnit p)).1 ha (mul_comm _ _)
  refine ⟨y, hpos, he, ?_⟩
  have hz : value e y pᶜ = 0 := by
    change (fixedEvaluation e y (pᶜ : ProjAlg A).val).re = 0
    rw [he]
    have hmul : p.val * (pᶜ : ProjAlg A).val = 0 := by
      change p.val * (1 - p.val) = 0
      rw [mul_sub, mul_one, p.isStarProjection.1, sub_self]
    rw [hmul, map_zero, Complex.zero_re]
  have hd := (null_iff_disjoint_support _ (value_continuous e y) (value_nonneg e hpos) pᶜ).mp hz
  have hh := hd.le_compl_left
  change (support (value e y)).val * (1 - (1 - p.val)) = (support (value e y)).val at hh
  change (support (value e y)).val * p.val = (support (value e y)).val
  simpa only [sub_sub_cancel] using hh

lemma positive_zero (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) : Positive e (0 : X) := by
  intro a ha
  simp [fixedEvaluation]

lemma support_zero (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) : support (value e (0 : X)) = ⊥ := by
  simp [support, value, fixedEvaluation] <;> rfl

lemma exists_positive_iSup (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (x : ℕ → X)
    (hx : ∀ n, Positive e (x n)) :
    ∃ y : X, Positive e y ∧ support (value e y) = ⨆ n, support (value e (x n)) := by
  letI := CStarAlgebra.spectralOrder A
  letI := CStarAlgebra.spectralOrderedRing A
  obtain ⟨y, hy⟩ := Gelfand39PredualSeries.exists_positive_sum e {a : A | 0 ≤ a} x
    (fun n a ha => hx n a ha)
  have hpos : Positive e y := fun a ha => (hy a ha).1
  refine ⟨y, hpos, ?_⟩
  apply support_iSup _ _ (fun n => value_continuous e (x n)) (value_continuous e y)
    (fun n => value_nonneg e (hx n)) (value_nonneg e hpos)
  intro p
  rw [value_zero_iff e hpos]
  have hp0 : 0 ≤ p.val := ((positiveUnit_iff_mem_Icc p.val).mp (projection_positiveUnit p)).1
  change Gelfand39PredualSeries.evaluation e p.val y = 0 ↔ _
  rw [(hy p.val hp0).2]
  exact forall_congr' (fun n => (value_zero_iff e (hx n) p).symm)

/-- A finite positive continuous valuation has exactly the same support as a
positive evaluation in the supplied predual. -/
theorem exists_positive_same_support (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (ν : ProjAlg A → ℝ) (hν : IsContinuousValuation ν) (hpν : ∀ p, 0 ≤ ν p) :
    ∃ y : X, Positive e y ∧ support (value e y) = support ν := by
  classical
  let pν : ProjAlg A := support ν
  let S : Set (ProjAlg A) := {p | ∃ x : X, Positive e x ∧ support (value e x) = p ∧ p ≤ pν}
  have hSne : S.Nonempty := ⟨⊥, 0, positive_zero e, support_zero e, bot_le⟩
  have hSdir : DirectedOn (· ≤ ·) S := by
    rintro p ⟨x, hx, hxp, hp⟩ q ⟨y, hy, hyq, hq⟩
    refine ⟨p ⊔ q, ⟨x + y, positive_add e hx hy, ?_, sup_le hp hq⟩, le_sup_left, le_sup_right⟩
    rw [support_add e hx hy, hxp, hyq]
  have hsp : S ⊆ Set.Iic pν := by
    rintro p ⟨x, hx, he, hp⟩
    exact hp
  have hStop : sSup S = pν := by
    apply le_antisymm (sSup_le hsp)
    by_contra hnot
    let r : ProjAlg A := pν ⊓ (sSup S)ᶜ
    have hr : r ≠ ⊥ := by
      intro hz
      apply hnot
      apply disjoint_compl_right_iff.mp
      exact disjoint_iff.mpr hz
    obtain ⟨x, hx, hxr⟩ := positive_evaluation_separates_projection e r hr
    obtain ⟨y, hy, he, hys⟩ := exists_positive_projection_vector e x hx r
    have hyr : fixedEvaluation e y r.val ≠ 0 := by
      rw [he, r.isStarProjection.1]
      exact hxr
    have hq : support (value e y) ∈ S := ⟨y, hy, rfl, hys.trans inf_le_left⟩
    have hle : support (value e y) ≤ sSup S := le_sSup hq
    have hcomp : support (value e y) ≤ (sSup S)ᶜ := hys.trans inf_le_right
    have hz : support (value e y) = ⊥ := by
      apply bot_unique
      calc
        support (value e y) ≤ sSup S ⊓ (sSup S)ᶜ := le_inf hle hcomp
        _ = ⊥ := inf_compl_eq_bot
    apply hyr
    apply (value_zero_iff e hy r).mp
    apply (null_iff_disjoint_support _ (value_continuous e y) (value_nonneg e hy) r).mpr
    rw [hz]
    exact disjoint_bot_right
  have hmono := valuation_monotone ν hν hpν
  have hstrict : StrictMonoOn ν (Set.Iic pν) :=
    Gelfand39FaithfulCover.strictMonoOn_of_faithful_on ν pν hν.1.1 hν.1.2 hpν
      (fun q hq hz => faithful_on_null_complement ν hpν hmono (null_sup_zero ν hν hpν) q hq hz)
  obtain ⟨f, hf, hfsup⟩ := Gelfand39FaithfulCover.exists_sequence_sup_on
    ν hmono pν hstrict S hSne hsp (valuation_sup ν hν hpν S hSne hSdir)
  change ∀ n, ∃ x : X, Positive e x ∧ support (value e x) = f n ∧ f n ≤ pν at hf
  choose x hx hxeq hle using hf
  obtain ⟨y, hy, hysup⟩ := exists_positive_iSup e x hx
  refine ⟨y, hy, ?_⟩
  calc
    support (value e y) = ⨆ n, support (value e (x n)) := hysup
    _ = ⨆ n, f n := iSup_congr hxeq
    _ = pν := hfsup.trans hStop
    _ = support ν := rfl

/-- A normal positive evaluation in the original predual detects every projection
that is non-null for the given positive valuation. -/
theorem exists_positive_dominating_nulls (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (ν : ProjAlg A → ℝ) (hν : IsContinuousValuation ν) (hpν : ∀ p, 0 ≤ ν p) :
    ∃ y : X, Positive e y ∧ ∀ p : ProjAlg A, value e y p = 0 → ν p = 0 := by
  obtain ⟨y, hy, he⟩ := exists_positive_same_support e ν hν hpν
  refine ⟨y, hy, ?_⟩
  intro p hp
  apply (null_iff_disjoint_support ν hν hpν p).mpr
  rw [← he]
  exact (null_iff_disjoint_support _ (value_continuous e y) (value_nonneg e hy) p).mp hp


end
end Gelfand39NormalMeasure
end Gelfand320WholeSource45

/- Source module Work.Gelfand39Multiplication; SHA256 3752dc998366a5896d2a48c12bb7b0fd0de30758983b4bbcdd130d89d7a61ca6. -/
section Gelfand320WholeSource46

set_option autoImplicit false

namespace Gelfand39ProjectionBand
open GelfandVNA.Duality Gelfand39Inverse WeakDual Gelfand39Predual
noncomputable section
universe u
variable {A X : Type u} [CommCStarAlgebra A] [WStarAlgebra A]
variable [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma continuous_multiplicationEvaluation_ball (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (x : X) (b : A) :
    Continuous (fun w : weakUnitBall X => fixedEvaluation e x (b * e (toStrongDual w.val))) := by
  let Φ := fixedEvaluation e x
  have hLip (w : weakUnitBall X) :
      LipschitzWith ‖Φ‖₊ (fun a : A => Φ (a * e (toStrongDual w.val))) := by
    apply LipschitzWith.of_dist_le_mul
    intro a c
    have hw : ‖e (toStrongDual w.val)‖ ≤ 1 := by
      rw [e.norm_map]
      exact w.property
    change dist (Φ (a * e (toStrongDual w.val))) (Φ (c * e (toStrongDual w.val))) ≤
      ‖Φ‖ * dist a c
    rw [dist_eq_norm, ← map_sub, ← sub_mul, dist_eq_norm]
    calc
      ‖Φ ((a - c) * e (toStrongDual w.val))‖ ≤ ‖Φ‖ * ‖(a - c) * e (toStrongDual w.val)‖ :=
        Φ.le_opNorm _
      _ ≤ ‖Φ‖ * (‖a - c‖ * ‖e (toStrongDual w.val)‖) :=
        mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg Φ)
      _ ≤ ‖Φ‖ * (‖a - c‖ * 1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw (norm_nonneg _)) (norm_nonneg Φ)
      _ = ‖Φ‖ * ‖a - c‖ := by rw [mul_one]
  have hF : Continuous (fun a : A => UniformFun.ofFun
      (fun w : weakUnitBall X => Φ (a * e (toStrongDual w.val)))) :=
    (UniformFun.lipschitzWith_ofFun_iff.mpr hLip).continuous
  let M : Submodule ℂ A := {
    carrier := {a | Continuous (fun w : weakUnitBall X => Φ (a * e (toStrongDual w.val)))}
    zero_mem' := by
      change Continuous (fun w : weakUnitBall X => Φ (0 * e (toStrongDual w.val)))
      simpa only [zero_mul, map_zero] using (continuous_const : Continuous (fun _ : weakUnitBall X => (0 : ℂ)))
    add_mem' := by
      intro a c ha hc
      change Continuous (fun w : weakUnitBall X => Φ ((a + c) * e (toStrongDual w.val)))
      apply (ha.add hc).congr
      intro w
      change Φ (a * e (toStrongDual w.val)) + Φ (c * e (toStrongDual w.val)) =
        Φ ((a + c) * e (toStrongDual w.val))
      rw [add_mul, map_add]
    smul_mem' := by
      intro c a ha
      change Continuous (fun w : weakUnitBall X => Φ ((c • a) * e (toStrongDual w.val)))
      apply (ha.const_smul c).congr
      intro w
      change c • Φ (a * e (toStrongDual w.val)) = Φ ((c • a) * e (toStrongDual w.val))
      rw [smul_mul_assoc, map_smul] }
  have hclosed : IsClosed (M : Set A) :=
    (UniformFun.isClosed_setOfPred_continuous (α := weakUnitBall X) (β := ℂ)).preimage hF
  have hspan : Submodule.span ℂ (Set.range (ProjAlg.val : ProjAlg A → A)) ≤ M := by
    apply Submodule.span_le.mpr
    rintro a ⟨p, rfl⟩
    exact continuous_projectionEvaluation_ball p e x
  have hd : Dense (M : Set A) := (projection_span_dense A).mono hspan
  have htop : (M : Set A) = Set.univ := by
    simpa only [hclosed.closure_eq] using hd.closure_eq
  have hb : b ∈ M := by
    change b ∈ (M : Set A)
    rw [htop]
    trivial
  exact hb

/-- Multiplication by any algebra element preserves the original predual. -/
theorem exists_multiplication_vector (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (x : X) (b : A) :
    ∃ y : X, ∀ a, fixedEvaluation e x (b * a) = fixedEvaluation e y a := by
  let Φ : A →L[ℂ] ℂ := {
    toFun a := fixedEvaluation e x (b * a)
    map_add' := by intro a c; rw [mul_add, map_add]
    map_smul' := by intro c a; rw [mul_smul_comm, map_smul]; rfl
    cont := by fun_prop }
  apply exists_predual_vector_of_weakStarContinuousOn_ball e Φ
  rw [← weakUnitBall_eq]
  exact continuousOn_iff_continuous_restrict.mpr (continuous_multiplicationEvaluation_ball e x b)

end
end Gelfand39ProjectionBand
end Gelfand320WholeSource46

/- Source module Work.Gelfand39ComplexAssembly; SHA256 afb91f5edf55cf4255607400c0986843a86c4434b0e6e549f2ae1d7a3eb10de0. -/
section Gelfand320WholeSource47

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GelfandVNA.Duality Gelfand311Jordan
open QAlgorithms.Papers.Independent.Support21.P20

namespace Gelfand39ComplexAssembly
universe u v
variable {A X : Type u} [CStarAlgebra A]
variable [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable {B : Type v} [CompleteBooleanAlgebra B]

/-- The four canonical Hahn--Jordan parts combine positive representations
inside one fixed predual. -/
theorem exists_complex_vector_of_positive (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (k : B → A)
    (hpositive : ∀ ρ : B → ℝ, IsContinuousValuation ρ → (∀ p, 0 ≤ ρ p) →
      ∃ x : X, ∀ p : B, star ((e.symm (k p)) x) = (ρ p : ℂ))
    (ν : B → ℂ) (hν : IsContinuousValuation ν) :
    ∃ x : X, ∀ p : B, star ((e.symm (k p)) x) = ν p := by
  have hj := (hahnJordan_decomposition B).2 ν
    (Or.inr ⟨fun _ => sup_compl_eq_top, hν⟩)
  rcases hj with ⟨hr, hi, hformula⟩
  rcases hr with ⟨_, _, _, _, hrp, hrm, hpr, hmr, _⟩
  rcases hi with ⟨_, _, _, _, hip, him, hpi, hmi, _⟩
  obtain ⟨x₁, hx₁⟩ := hpositive _ hrp.1 hpr
  obtain ⟨x₂, hx₂⟩ := hpositive _ hrm.1 hmr
  obtain ⟨x₃, hx₃⟩ := hpositive _ hip.1 hpi
  obtain ⟨x₄, hx₄⟩ := hpositive _ him.1 hmi
  let x : X := (x₁ - x₂) + star Complex.I • (x₃ - x₄)
  refine ⟨x, ?_⟩
  intro p
  have heq : star ((e.symm (k p)) x) =
      star ((e.symm (k p)) x₁) - star ((e.symm (k p)) x₂) +
      Complex.I * (star ((e.symm (k p)) x₃) - star ((e.symm (k p)) x₄)) := by
    dsimp [x]
    simp only [map_add, map_sub, map_smul, starRingEnd_apply, star_add, star_sub,
      star_smul, star_mul, star_star, smul_eq_mul] <;> ring
  rw [heq, hx₁, hx₂, hx₃, hx₄]
  exact (hformula p).symm

end Gelfand39ComplexAssembly
end
end Gelfand320WholeSource47

/- Source module Work.Gelfand39Complete; SHA256 6c4d94efb700b914ca12ed99911f79be1d4c18a5f7a0a6cbdffd210da952d7ea. -/
section Gelfand320WholeSource48

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GelfandVNA.Duality Gelfand39ProjectionBand
open QAlgorithms.Papers.Independent.Support21.P20

namespace Gelfand39Complete
universe u
variable {A X : Type u} [CommCStarAlgebra A] [WStarAlgebra A]
variable [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem positive_extension_exists_vector (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (ν : ProjAlg A → ℝ) (hν : IsContinuousValuation ν) (hpν : ∀ p, 0 ≤ ν p)
    (Ψ : A →L[ℂ] ℂ) (hΨ : ∀ p : ProjAlg A, Ψ p.val = (ν p : ℂ)) :
    ∃ x : X, ∀ a : A, Ψ a = star ((e.symm a) x) := by
  letI := CStarAlgebra.spectralOrder A
  letI := CStarAlgebra.spectralOrderedRing A
  letI := Gelfand39NormalJordan.projectionCompleteBooleanAlgebra A
  obtain ⟨y, hy, hac⟩ := Gelfand39NormalMeasure.exists_positive_dominating_nulls e ν hν hpν
  let μ : ProjAlg A → ℝ := Gelfand39NormalMeasure.value e y
  let Φ : A →L[ℂ] ℂ := fixedEvaluation e y
  have hμ : IsContinuousValuation μ := Gelfand39NormalMeasure.value_continuous e y
  have hpμ : ∀ p, 0 ≤ μ p := Gelfand39NormalMeasure.value_nonneg e hy
  have hΦ (p : ProjAlg A) : Φ p.val = (μ p : ℂ) := by
    apply Complex.ext
    · rfl
    · exact (Complex.nonneg_iff.mp
        (Gelfand39NormalMeasure.evaluation_projection_nonneg e hy p)).2.symm
  have hΦmult (b : A) : ∃ x : X, ∀ a : A,
      Φ (star b * a) = star ((e.symm a) x) := by
    obtain ⟨x, hx⟩ := exists_multiplication_vector e y (star b)
    exact ⟨x, hx⟩
  exact Gelfand39Truncation.exists_predual_vector_of_absolute_continuity e μ ν
    hμ hν hpμ hpν Φ Ψ hΦ hΨ hΦmult hac

theorem positive_valuation_exists_vector (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (ν : ProjAlg A → ℝ) (hν : IsContinuousValuation ν) (hpν : ∀ p, 0 ≤ ν p) :
    ∃ x : X, ∀ p : ProjAlg A, star ((e.symm p.val) x) = (ν p : ℂ) := by
  letI := Gelfand39NormalJordan.projectionCompleteBooleanAlgebra A
  obtain ⟨Ψ, hΨ, _⟩ := Gelfand39Inverse.positive_valuation_bounded_extension ν hν.1.1
    (Gelfand39ValuationSup.disjoint_add ν hν.1) hpν
  obtain ⟨x, hx⟩ := positive_extension_exists_vector e ν hν hpν Ψ hΨ
  exact ⟨x, fun p => (hx p.val).symm.trans (hΨ p)⟩

end Gelfand39Complete

namespace GelfandVNA.Duality
universe u

/-- Restriction to projections identifies normal functionals with complex
continuous valuations. -/
theorem proposition_3_9 (A : Type u) [CommCStarAlgebra A] [WStarAlgebra A] :
    (∀ φ : A → ℂ, IsNormalFunctional φ → IsContinuousValuation (fun p : ProjAlg A => φ p.val)) ∧
    (∀ ν : ProjAlg A → ℂ, IsContinuousValuation ν →
      ∃! φ : A → ℂ, IsNormalFunctional φ ∧ ∀ p : ProjAlg A, φ p.val = ν p) := by
  refine ⟨Gelfand39.normal_restrict_isContinuousValuation, ?_⟩
  intro ν hν
  obtain ⟨X, hX, hN, hC, ⟨e⟩⟩ := WStarAlgebra.exists_predual (M := A)
  letI := Gelfand39NormalJordan.projectionCompleteBooleanAlgebra A
  obtain ⟨x, hx⟩ := Gelfand39ComplexAssembly.exists_complex_vector_of_positive e
    (ProjAlg.val : ProjAlg A → A) (Gelfand39Complete.positive_valuation_exists_vector e) ν hν
  let φ : A → ℂ := fun a => star ((e.symm a) x)
  have hφ : IsNormalFunctional φ :=
    ⟨X, inferInstance, inferInstance, inferInstance, e, x, fun _ => rfl⟩
  refine ⟨φ, ⟨hφ, hx⟩, ?_⟩
  intro ψ hψ
  exact Gelfand39Inverse.normal_functionals_ext_projections ψ φ hψ.1 hφ
    (fun p => (hψ.2 p).trans (hx p).symm)

end GelfandVNA.Duality
end
end Gelfand320WholeSource48

/- Source module Work.Gelfand320.ProjectionSource; SHA256 ecf4c48b8f8a11a9d182d742f567790c01113c324b332f935bf136434c23557b. -/
section Gelfand320WholeSource49

/- Projection and localizability helpers reused verbatim from accepted lemma3.11,
submission3760d494-b769-4852-b572-31335a8bbbeb. Only imports/#print commands removed. -/

section

set_option autoImplicit false

namespace Gelfand311

open Gelfand38 Gelfand39 GelfandVNA.Duality WeakDual Set Filter
open QAlgorithms.Papers.Independent.Support21.P20
open scoped Topology

universe u
variable {A B : Type u} [CommCStarAlgebra A] [CommCStarAlgebra B]

lemma projection_ext {p q : ProjAlg A} (h : p.val = q.val) : p = q :=
  Subtype.ext (Subtype.ext h)

lemma projMap_inf (f : A →⋆ₐ[ℂ] B) (p q : ProjAlg A) :
    projMap f (p ⊓ q) = projMap f p ⊓ projMap f q := by
  apply projection_ext
  exact map_mul f p.val q.val

lemma projMap_sup (f : A →⋆ₐ[ℂ] B) (p q : ProjAlg A) :
    projMap f (p ⊔ q) = projMap f p ⊔ projMap f q := by
  apply projection_ext
  change f (p.val + q.val - p.val * q.val) = f p.val + f q.val - f p.val * f q.val
  simp

lemma projMap_compl (f : A →⋆ₐ[ℂ] B) (p : ProjAlg A) :
    projMap f pᶜ = (projMap f p)ᶜ := by
  apply projection_ext
  change f (1 - p.val) = 1 - f p.val
  simp

lemma projMap_bot (f : A →⋆ₐ[ℂ] B) : projMap f ⊥ = ⊥ :=
  projection_ext (map_zero f)

lemma projMap_top (f : A →⋆ₐ[ℂ] B) : projMap f ⊤ = ⊤ :=
  projection_ext (map_one f)

lemma projMap_mono (f : A →⋆ₐ[ℂ] B) : Monotone (projMap f) := by
  intro p q hpq
  change p.val * q.val = p.val at hpq
  change f p.val * f q.val = f p.val
  rw [← map_mul, hpq]

lemma projMap_finset_sup (f : A →⋆ₐ[ℂ] B) {ι : Type*} (t : Finset ι) (g : ι → ProjAlg A) :
    projMap f (t.sup g) = t.sup (fun i => projMap f (g i)) := by
  classical
  induction t using Finset.induction_on with
  | empty => exact projMap_bot f
  | @insert i t hit ih => simp only [Finset.sup_insert, projMap_sup, ih]

theorem projMap_directed_isLUB [WStarAlgebra B] (f : A →⋆ₐ[ℂ] B) (hf : IsNormalStarHom f)
    (s : Set (ProjAlg A)) (hs : s.Nonempty) (hd : DirectedOn (· ≤ ·) s)
    (a : ProjAlg A) (ha : IsLUB s a) : IsLUB (projMap f '' s) (projMap f a) := by
  classical
  let t : Set (ProjAlg B) := projMap f '' s
  have ht : t.Nonempty := hs.image _
  have htd : DirectedOn (· ≤ ·) t := by
    rintro p ⟨p', hp', rfl⟩ q ⟨q', hq', rfl⟩
    obtain ⟨r, hr, hpr, hqr⟩ := hd p' hp' q' hq'
    exact ⟨projMap f r, ⟨r, hr, rfl⟩, projMap_mono f hpr, projMap_mono f hqr⟩
  obtain ⟨b, hb⟩ := projections_complete t
  let : Nonempty s := hs.to_subtype
  let : IsDirectedOrder s := hd.isDirectedOrder
  let g : s → t := fun p => ⟨projMap f p.val, ⟨p.val, p.property, rfl⟩⟩
  have hg : Tendsto g atTop atTop := by
    apply Monotone.tendsto_atTop_atTop
    · intro p q hpq
      exact projMap_mono f hpq
    · rintro ⟨q, ⟨p, hp, rfl⟩⟩
      exact ⟨⟨p, hp⟩, le_rfl⟩
  obtain ⟨X, hX, hN, hC, ⟨e⟩⟩ := WStarAlgebra.exists_predual (M := B)
  have hval : (projMap f a).val = b.val := by
    apply e.symm.injective
    apply ContinuousLinearMap.ext
    intro x
    let φ : B → ℂ := fun z => star ((e.symm z) x)
    have hφ : IsNormalFunctional φ := ⟨X, hX, hN, hC, e, x, fun _ => rfl⟩
    have hsource := (normal_restrict_isContinuousValuation (φ ∘ f) (hf φ hφ)).2 s a hs hd ha
    have htarget := ((normal_restrict_isContinuousValuation φ hφ).2 t b ht htd hb).comp hg
    have hsource' : Tendsto (fun p : s => φ (f p.val.val)) atTop (𝓝 (φ (f a.val))) := hsource
    have htarget' : Tendsto (fun p : s => φ (f p.val.val)) atTop (𝓝 (φ b.val)) := htarget
    have heq := tendsto_nhds_unique hsource' htarget'
    exact star_injective heq
  have heq : projMap f a = b := projection_ext hval
  rw [heq]
  exact hb

theorem projMap_isLUB [WStarAlgebra B] (f : A →⋆ₐ[ℂ] B) (hf : IsNormalStarHom f)
    (s : Set (ProjAlg A)) (a : ProjAlg A) (ha : IsLUB s a) :
    IsLUB (projMap f '' s) (projMap f a) := by
  classical
  let joins : Finset s → ProjAlg A := fun t => t.sup Subtype.val
  let d : Set (ProjAlg A) := Set.range joins
  have hdne : d.Nonempty := ⟨joins ∅, ⟨∅, rfl⟩⟩
  have hddir : DirectedOn (· ≤ ·) d := by
    rintro p ⟨t, rfl⟩ q ⟨u, rfl⟩
    exact ⟨joins (t ∪ u), ⟨t ∪ u, rfl⟩,
      Finset.sup_mono Finset.subset_union_left, Finset.sup_mono Finset.subset_union_right⟩
  have hda : IsLUB d a := by
    constructor
    · rintro p ⟨t, rfl⟩
      exact Finset.sup_le (fun p hp => ha.1 p.property)
    · intro p hp
      apply ha.2
      intro q hq
      have hh := hp (show joins {⟨q, hq⟩} ∈ d from ⟨{⟨q, hq⟩}, rfl⟩)
      simpa [joins] using hh
  have hmap := projMap_directed_isLUB f hf d hdne hddir a hda
  constructor
  · rintro p ⟨q, hq, rfl⟩
    exact projMap_mono f (ha.1 hq)
  · intro p hp
    apply hmap.2
    rintro q ⟨r, ⟨t, rfl⟩, rfl⟩
    change projMap f (t.sup Subtype.val) ≤ p
    rw [projMap_finset_sup]
    exact Finset.sup_le (fun q hq => hp ⟨q.val, q.property, rfl⟩)

theorem normal_projMap_complete [WStarAlgebra A] [WStarAlgebra B]
    (f : A →⋆ₐ[ℂ] B) (hf : IsNormalStarHom f) :
    (∀ p q : ProjAlg A, projMap f (p ⊓ q) = projMap f p ⊓ projMap f q) ∧
    (∀ p q : ProjAlg A, projMap f (p ⊔ q) = projMap f p ⊔ projMap f q) ∧
    (∀ p : ProjAlg A, projMap f pᶜ = (projMap f p)ᶜ) ∧
    projMap f ⊥ = ⊥ ∧ projMap f ⊤ = ⊤ ∧
    (∀ (s : Set (ProjAlg A)) (a : ProjAlg A), IsLUB s a →
      IsLUB (projMap f '' s) (projMap f a)) :=
  ⟨projMap_inf f, projMap_sup f, projMap_compl f, projMap_bot f, projMap_top f,
    projMap_isLUB f hf⟩


end Gelfand311

end

section

set_option autoImplicit false

namespace Gelfand311

open Gelfand38 Gelfand39 GelfandVNA.Duality WeakDual Set Filter
open QAlgorithms.Papers.Independent.Support21.P20
open scoped Topology NNReal

universe u

noncomputable def projectionCompleteBooleanAlgebra (A : Type u) [CommCStarAlgebra A]
    [WStarAlgebra A] : CompleteBooleanAlgebra (ProjAlg A) := by
  let sup : Set (ProjAlg A) → ProjAlg A := fun s => (projections_complete s).choose
  have hsup (s : Set (ProjAlg A)) : IsLUB s (sup s) := (projections_complete s).choose_spec
  exact {
    (inferInstance : BooleanAlgebra (ProjAlg A)) with
    sSup := sup
    sInf := fun s => sup (lowerBounds s)
    isLUB_sSup := hsup
    isGLB_sInf := fun s => isLUB_lowerBounds.mp (hsup (lowerBounds s)) }

lemma real_normal_to_positive {L : Type*} [Order.Frame L] (ν : L → ℝ)
    (hν : IsNormalValuation ν) (hpos : ∀ a, 0 ≤ ν a) :
    IsPositiveContinuousValuation (fun a => (⟨ν a, hpos a⟩ : ℝ≥0)) := by
  let μ : L → ℝ≥0 := fun a => ⟨ν a, hpos a⟩
  have hmono : Monotone μ := by
    intro a b hab
    change ν a ≤ ν b
    have hh := Gelfand311Jordan.g72gk34_split hν hab
    linarith [hpos (b ⊓ aᶜ)]
  refine ⟨⟨Subtype.ext hν.1.1.1, fun a b => Subtype.ext (hν.1.1.2 a b)⟩, hmono, ?_⟩
  intro s a hs hd ha
  let : Nonempty s := hs.to_subtype
  let : IsDirectedOrder s := hd.isDirectedOrder
  have ht : Tendsto (fun b : s => μ b.val) atTop (𝓝 (μ a)) :=
    tendsto_subtype_rng.mpr (hν.1.2 s a hs hd ha)
  have hl := isLUB_of_tendsto_atTop (fun (p q : s) hpq => hmono hpq) ht
  have he : Set.range (fun p : s => μ p.val) = μ '' s := by
    ext z
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.val, p.property, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, rfl⟩
  rw [he] at hl
  exact hl

lemma complex_valuation_positive_witness (L : Type*) [CompleteBooleanAlgebra L]
    (ν : L → ℂ) (hν : IsContinuousValuation ν) (p : L) (hp : ν p ≠ 0) :
    ∃ μ : L → ℝ≥0, IsPositiveContinuousValuation μ ∧ μ p ≠ 0 := by
  have hj := (Gelfand311Jordan.hahnJordan_decomposition L).2 ν
    (Or.inr ⟨fun a => sup_compl_eq_top, hν⟩)
  rcases hj with ⟨hr, hi, heq⟩
  rcases hr with ⟨_, _, _, _, hrpn, hrmn, hrp, hrm, _⟩
  rcases hi with ⟨_, _, _, _, hipn, himn, hip, him, _⟩
  have hn : jordanPositive (fun a => (ν a).re) p ≠ 0 ∨
      jordanNegative (fun a => (ν a).re) p ≠ 0 ∨
      jordanPositive (fun a => (ν a).im) p ≠ 0 ∨
      jordanNegative (fun a => (ν a).im) p ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hp
    rw [heq p, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2]
    simp
  have helper (r : L → ℝ) (hr : IsNormalValuation r) (hpos : ∀ a, 0 ≤ r a)
      (hne : r p ≠ 0) : ∃ μ : L → ℝ≥0, IsPositiveContinuousValuation μ ∧ μ p ≠ 0 := by
    refine ⟨fun a => ⟨r a, hpos a⟩, real_normal_to_positive r hr hpos, ?_⟩
    intro hzero
    exact hne (congrArg (fun z : ℝ≥0 => (z : ℝ)) hzero)
  rcases hn with hn | hn | hn | hn
  · exact helper _ hrpn hrp hn
  · exact helper _ hrmn hrm hn
  · exact helper _ hipn hip hn
  · exact helper _ himn him hn

theorem projections_localizable (A : Type u) [CommCStarAlgebra A] [WStarAlgebra A] :
    letI := projectionCompleteBooleanAlgebra A
    HasFiniteValuationCover (ProjAlg A) := by
  let := projectionCompleteBooleanAlgebra A
  apply (Gelfand273Criterion.localizableCriterion (ProjAlg A)).2
  intro p hp
  obtain ⟨X, hX, hN, hC, ⟨e⟩⟩ := WStarAlgebra.exists_predual (M := A)
  have hdual : e.symm p.val ≠ 0 := by
    intro hzero
    apply hp
    apply projection_ext
    change p.val = 0
    apply e.symm.injective
    simpa only [map_zero] using hzero
  obtain ⟨x, hx⟩ : ∃ x : X, (e.symm p.val) x ≠ 0 := by
    by_contra h
    push Not at h
    apply hdual
    ext x
    exact h x
  let φ : A → ℂ := fun a => star ((e.symm a) x)
  have hφ : IsNormalFunctional φ := ⟨X, hX, hN, hC, e, x, fun _ => rfl⟩
  have hn : φ p.val ≠ 0 := by
    intro hzero
    exact hx (star_eq_zero.mp hzero)
  exact complex_valuation_positive_witness (ProjAlg A) (fun q => φ q.val)
    (normal_restrict_isContinuousValuation φ hφ) p hn


end Gelfand311

end
end Gelfand320WholeSource49

/- Source module Work.Gelfand320.ProjectionFunctor; SHA256 76ea12c2f438589c29e4ad85edf92d91649e42f9ef54e95b566dda3207a57289. -/
section Gelfand320WholeSource50

set_option autoImplicit false

namespace Gelfand320
open CategoryTheory Opposite GelfandVNA.Duality
open scoped CStarAlgebra
noncomputable section
universe u

/-- The measurable locale of projections, with its canonical Boolean operations. -/
def projectionObj (A : CVNA.{u}) : MLoc.{u} :=
  show MLocObj from
    { carrier := ProjAlg A.carrier
      cba := Gelfand311.projectionCompleteBooleanAlgebra A.carrier
      localizable := Gelfand311.projections_localizable A.carrier }

/-- Restriction of a normal star homomorphism preserves arbitrary joins and finite meets. -/
def projectionFrameHom {A B : CVNA.{u}} (f : A ⟶ B) :
    FrameHom (projectionObj A).carrier (projectionObj B).carrier := by
  letI := Gelfand311.projectionCompleteBooleanAlgebra A.carrier
  letI := Gelfand311.projectionCompleteBooleanAlgebra B.carrier
  exact {
    toFun := projMap f.1
    map_top' := Gelfand311.projMap_top f.1
    map_inf' := Gelfand311.projMap_inf f.1
    map_sSup' s := (Gelfand311.projMap_isLUB f.1 f.2 s (sSup s) (isLUB_sSup s)).unique
      (isLUB_sSup _) }

/-- The projection-locale functor appearing in the exact theorem3.20 statement. -/
def projectionFunctor : CVNA.{u}ᵒᵖ ⥤ MLoc.{u} where
  obj A := projectionObj A.unop
  map f := InducedCategory.homMk (Frm.ofHom (projectionFrameHom f.unop)).op
  map_id _ := rfl
  map_comp f g := by
    apply InducedCategory.hom_ext
    apply Quiver.Hom.unop_inj
    apply Frm.hom_ext
    ext p
    rfl

/-- A star homomorphism is determined by its restriction to projections. -/
theorem starAlgHom_eq_of_projections {A B : Type u} [CommCStarAlgebra A]
    [WStarAlgebra A] [CommCStarAlgebra B] (f g : A →⋆ₐ[ℂ] B)
    (h : ∀ p : ProjAlg A, f p.val = g p.val) : f = g := by
  let F : A →L[ℂ] B := { f.toAlgHom.toLinearMap with cont := map_continuous f }
  let G : A →L[ℂ] B := { g.toAlgHom.toLinearMap with cont := map_continuous g }
  have he : F = G := by
    apply ContinuousLinearMap.ext_on (Gelfand39Inverse.projection_span_dense A)
    rintro a ⟨p, rfl⟩
    exact h p
  ext a
  exact congrArg (fun F : A →L[ℂ] B => F a) he

instance projectionFunctor_faithful : projectionFunctor.{u}.Faithful where
  map_injective := by
    intro A B f g hfg
    apply Quiver.Hom.unop_inj
    apply Subtype.ext
    apply starAlgHom_eq_of_projections
    intro p
    have hh := congrArg (fun k : projectionFunctor.obj A ⟶ projectionFunctor.obj B =>
      ProjAlg.val (A := A.unop.carrier) (MLoc.frameHom k p)) hfg
    exact hh

/-- The exact naturality constraint is definitional for the constructed functor. -/
theorem projectionFunctor_map {A B : CVNA.{u}} (f : A ⟶ B)
    (p : (projectionFunctor.obj (op A)).carrier) :
    ProjAlg.val (A := B.carrier) (MLoc.frameHom (projectionFunctor.map f.op) p) =
      f.1 (ProjAlg.val (A := A.carrier) p) := rfl


end
end Gelfand320
end Gelfand320WholeSource50

/- Source module Work.Gelfand320.LinearLift; SHA256 65eb030c6627051f078583193fe9810ac8053e5fbd7db75fa5c7721afa52cc87. -/
section Gelfand320WholeSource51

set_option autoImplicit false
namespace Gelfand320
open GelfandVNA.Duality Gelfand38 Gelfand39Inverse WeakDual
open scoped BigOperators
noncomputable section
universe u
variable {A B : Type u} [CommCStarAlgebra A] [CommCStarAlgebra B]

/-- Every character of the target gives a positive finitely additive valuation of mass one. -/
def characterValuation (h : BoundedLatticeHom (ProjAlg A) (ProjAlg B))
    (χ : characterSpace ℂ B) (p : ProjAlg A) : ℝ :=
  (gelfandTransform ℂ B (h p).val χ).re

lemma characterValuation_nonneg (h : BoundedLatticeHom (ProjAlg A) (ProjAlg B))
    (χ : characterSpace ℂ B) (p : ProjAlg A) : 0 ≤ characterValuation h χ p := by
  rcases projection_value_zero_or_one (h p) χ with he | he <;>
    simp [characterValuation, he]

lemma characterValuation_zero (h : BoundedLatticeHom (ProjAlg A) (ProjAlg B))
    (χ : characterSpace ℂ B) : characterValuation h χ ⊥ = 0 := by
  simp only [characterValuation, map_bot]
  change (gelfandTransform ℂ B 0 χ).re = 0
  simp

lemma characterValuation_top (h : BoundedLatticeHom (ProjAlg A) (ProjAlg B))
    (χ : characterSpace ℂ B) : characterValuation h χ ⊤ = 1 := by
  simp only [characterValuation, map_top]
  change (gelfandTransform ℂ B 1 χ).re = 1
  simp

lemma characterValuation_add (h : BoundedLatticeHom (ProjAlg A) (ProjAlg B))
    (χ : characterSpace ℂ B) (p q : ProjAlg A) (hpq : Disjoint p q) :
    characterValuation h χ (p ⊔ q) = characterValuation h χ p + characterValuation h χ q := by
  have hm : (h p).val * (h q).val = 0 := by
    change (h p ⊓ h q).val = (⊥ : ProjAlg B).val
    rw [← map_inf, hpq.eq_bot, map_bot]
  simp only [characterValuation, map_sup]
  change (gelfandTransform ℂ B ((h p).val + (h q).val - (h p).val * (h q).val) χ).re = _
  simp [hm]

lemma characterValuation_value (h : BoundedLatticeHom (ProjAlg A) (ProjAlg B))
    (χ : characterSpace ℂ B) (p : ProjAlg A) :
    gelfandTransform ℂ B (h p).val χ = (characterValuation h χ p : ℂ) := by
  rcases projection_value_zero_or_one (h p) χ with he | he <;>
    simp [characterValuation, he]

/-- A Boolean homomorphism is contractive on the algebraic span of projections. -/
theorem mapped_projection_sum_norm_le (h : BoundedLatticeHom (ProjAlg A) (ProjAlg B))
    (c : ProjAlg A →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ (fun p => (h p).val) c‖ ≤
      ‖Finsupp.linearCombination ℂ (ProjAlg.val : ProjAlg A → A) c‖ := by
  classical
  rw [← gelfand_norm]
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
  intro χ
  have hb := projection_linearCombination_bound (characterValuation h χ)
    (characterValuation_zero h χ) (characterValuation_add h χ)
    (characterValuation_nonneg h χ) c
  rw [characterValuation_top, one_mul] at hb
  have he : gelfandTransform ℂ B (Finsupp.linearCombination ℂ (fun p => (h p).val) c) χ =
      Finsupp.linearCombination ℂ (fun p => (characterValuation h χ p : ℂ)) c := by
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
      ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro p hp
    rw [characterValuation_value]
  rw [he]
  exact hb

/-- The finite projection map extends uniquely to a bounded complex-linear map. -/
theorem exists_unique_linear_lift [WStarAlgebra A]
    (h : BoundedLatticeHom (ProjAlg A) (ProjAlg B)) :
    ∃! Φ : A →L[ℂ] B, ∀ p : ProjAlg A, Φ p.val = (h p).val := by
  let f := Finsupp.linearCombination ℂ (fun p : ProjAlg A => (h p).val)
  let e := Finsupp.linearCombination ℂ (ProjAlg.val : ProjAlg A → A)
  have hd : DenseRange e := projection_linearCombination_dense
  have hb : ∃ C : ℝ, ∀ c, ‖f c‖ ≤ C * ‖e c‖ :=
    ⟨1, fun c => by simpa only [one_mul] using mapped_projection_sum_norm_le h c⟩
  refine ⟨f.extendOfNorm e, ?_, ?_⟩
  · intro p
    have hh := LinearMap.extendOfNorm_eq hd hb (Finsupp.single p (1 : ℂ))
    simpa only [f, e, Finsupp.linearCombination_single, one_smul] using hh
  · intro Φ hΦ
    apply ContinuousLinearMap.ext_on (projection_span_dense A)
    rintro a ⟨p, rfl⟩
    rw [hΦ p]
    have hh := LinearMap.extendOfNorm_eq hd hb (Finsupp.single p (1 : ℂ))
    simpa only [f, e, Finsupp.linearCombination_single, one_smul] using hh.symm

end
end Gelfand320
end Gelfand320WholeSource51

/- Source module Work.Gelfand320.StarLift; SHA256 7fef767da9e1f965f3eaadec1559312f12e49abceb1e5e61e5b2a79916edb282. -/
section Gelfand320WholeSource52

set_option autoImplicit false
namespace Gelfand320
open GelfandVNA.Duality Gelfand39Inverse
noncomputable section
universe u
variable {A B : Type u} [CommCStarAlgebra A] [WStarAlgebra A] [CommCStarAlgebra B]

/-- Multiplicativity extends from projection products by density in each argument. -/
lemma linear_lift_mul (h : BoundedLatticeHom (ProjAlg A) (ProjAlg B))
    (Φ : A →L[ℂ] B) (hΦ : ∀ p : ProjAlg A, Φ p.val = (h p).val) (a b : A) :
    Φ (a * b) = Φ a * Φ b := by
  have hp (p : ProjAlg A) : Φ.comp (ContinuousLinearMap.mul ℂ A p.val) =
      (ContinuousLinearMap.mul ℂ B (Φ p.val)).comp Φ := by
    apply ContinuousLinearMap.ext_on (projection_span_dense A)
    rintro x ⟨q, rfl⟩
    change Φ (p.val * q.val) = Φ p.val * Φ q.val
    change Φ (p ⊓ q).val = _
    rw [hΦ, map_inf, hΦ p, hΦ q]
    rfl
  have he : Φ.comp ((ContinuousLinearMap.mul ℂ A).flip b) =
      ((ContinuousLinearMap.mul ℂ B).flip (Φ b)).comp Φ := by
    apply ContinuousLinearMap.ext_on (projection_span_dense A)
    rintro x ⟨p, rfl⟩
    exact congrArg (fun F : A →L[ℂ] B => F b) (hp p)
  exact congrArg (fun F : A →L[ℂ] B => F a) he

/-- Conjugating domain and codomain stars gives another complex-linear map;
projection density identifies it with the original extension. -/
lemma linear_lift_star (h : BoundedLatticeHom (ProjAlg A) (ProjAlg B))
    (Φ : A →L[ℂ] B) (hΦ : ∀ p : ProjAlg A, Φ p.val = (h p).val) (a : A) :
    Φ (star a) = star (Φ a) := by
  let Ψ : A →L[ℂ] B :=
    { toFun := fun a => star (Φ (star a))
      map_add' := by intro a b; simp only [star_add, map_add]
      map_smul' := by intro c a; simp only [star_smul, map_smul, star_star, RingHom.id_apply]
      cont := by fun_prop }
  have he : Ψ = Φ := by
    apply ContinuousLinearMap.ext_on (projection_span_dense A)
    rintro x ⟨p, rfl⟩
    change star (Φ (star p.val)) = Φ p.val
    rw [p.isStarProjection.2, hΦ p, (h p).isStarProjection.2]
  have he' := congrArg (fun F : A →L[ℂ] B => F (star a)) he
  change star (Φ (star (star a))) = Φ (star a) at he'
  simpa only [star_star] using he'.symm

/-- Every Boolean homomorphism on projections has a unique unital star-algebra lift. -/
theorem exists_starAlgHom_lift (h : BoundedLatticeHom (ProjAlg A) (ProjAlg B)) :
    ∃ f : A →⋆ₐ[ℂ] B, ∀ p : ProjAlg A, f p.val = (h p).val := by
  obtain ⟨Φ, hΦ, _⟩ := exists_unique_linear_lift h
  have h1 : Φ 1 = 1 := by
    have hh := hΦ ⊤
    rw [map_top] at hh
    exact hh
  refine ⟨{ toFun := Φ
            map_zero' := Φ.map_zero
            map_one' := h1
            map_add' := Φ.map_add
            map_mul' := linear_lift_mul h Φ hΦ
            commutes' := ?_
            map_star' := linear_lift_star h Φ hΦ }, hΦ⟩
  intro c
  rw [Algebra.algebraMap_eq_smul_one, map_smul, h1, Algebra.algebraMap_eq_smul_one]

end
end Gelfand320
end Gelfand320WholeSource52

/- Source module Work.Gelfand320.Full; SHA256 4bc57237ea29c2805e7c671991889b66fa397ff3ffc375341163722317d73e03. -/
section Gelfand320WholeSource53

set_option autoImplicit false
namespace Gelfand320
open Set CategoryTheory Opposite GelfandVNA.Duality
open Filter hiding map_inf map_sup map_top map_bot
open QAlgorithms.Papers.Independent.Support21.P20
open scoped Topology CStarAlgebra
noncomputable section
universe u

/-- Directed continuity of a valuation is preserved by precomposition with a frame map. -/
theorem valuation_comp_frameHom {L M : Type u} [CompleteBooleanAlgebra L]
    [CompleteBooleanAlgebra M] (h : FrameHom L M) (ν : M → ℂ)
    (hν : IsContinuousValuation ν) : IsContinuousValuation (ν ∘ h) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simpa only [Function.comp_apply, map_bot] using hν.1.1
  · intro a b
    simpa only [Function.comp_apply, map_inf, map_sup] using hν.1.2 (h a) (h b)
  · intro s a hs hd ha
    let t : Set M := h '' s
    have ht : t.Nonempty := hs.image h
    have htd : DirectedOn (· ≤ ·) t := by
      rintro x ⟨p, hp, rfl⟩ y ⟨q, hq, rfl⟩
      obtain ⟨r, hr, hpr, hqr⟩ := hd p hp q hq
      exact ⟨h r, ⟨r, hr, rfl⟩, OrderHomClass.mono h hpr, OrderHomClass.mono h hqr⟩
    have hta : IsLUB t (h a) := by
      rw [ha.unique (isLUB_sSup s), map_sSup]
      exact isLUB_sSup t
    letI : Nonempty s := hs.to_subtype
    letI : Nonempty t := ht.to_subtype
    letI : IsDirectedOrder s := hd.isDirectedOrder
    letI : IsDirectedOrder t := htd.isDirectedOrder
    let k : s → t := fun p => ⟨h p.val, p.val, p.property, rfl⟩
    have hk : Tendsto k atTop atTop := by
      apply tendsto_atTop.2
      rintro ⟨q, p, hp, rfl⟩
      filter_upwards [eventually_ge_atTop (⟨p, hp⟩ : s)] with r hr
      exact OrderHomClass.mono h hr
    exact (hν.2 t (h a) ht htd hta).comp hk

variable {A B : Type u} [CommCStarAlgebra A] [WStarAlgebra A]
  [CommCStarAlgebra B] [WStarAlgebra B]
local instance : CompleteBooleanAlgebra (ProjAlg A) := Gelfand311.projectionCompleteBooleanAlgebra A
local instance : CompleteBooleanAlgebra (ProjAlg B) := Gelfand311.projectionCompleteBooleanAlgebra B

def frameBooleanHom (h : FrameHom (ProjAlg A) (ProjAlg B)) :
    BoundedLatticeHom (ProjAlg A) (ProjAlg B) where
  toFun := h
  map_sup' := map_sup h
  map_inf' := map_inf h
  map_top' := h.map_top'
  map_bot' := by
    have hh := h.map_sSup' (∅ : Set (ProjAlg A))
    simp only [Set.image_empty, sSup_empty] at hh
    exact hh

/-- Exact proposition3.9 identifies the pullback functional as normal. -/
theorem star_lift_normal (h : FrameHom (ProjAlg A) (ProjAlg B))
    (f : A →⋆ₐ[ℂ] B) (hf : ∀ p : ProjAlg A, f p.val = (h p).val) :
    IsNormalStarHom f := by
  intro φ hφ
  have hν : IsContinuousValuation (fun p : ProjAlg A => φ (h p).val) :=
    valuation_comp_frameHom h (fun p : ProjAlg B => φ p.val)
      ((GelfandVNA.Duality.proposition_3_9 B).1 φ hφ)
  obtain ⟨ψ, ⟨hψ, hψp⟩, _⟩ := (GelfandVNA.Duality.proposition_3_9 A).2 _ hν
  obtain ⟨Φ, hΦ⟩ := Gelfand39Inverse.normal_functional_existsCLM φ hφ
  obtain ⟨Ψ, hΨ⟩ := Gelfand39Inverse.normal_functional_existsCLM ψ hψ
  let F : A →L[ℂ] B := { f.toAlgHom.toLinearMap with cont := map_continuous f }
  have he : Φ.comp F = Ψ := by
    apply ContinuousLinearMap.ext_on (Gelfand39Inverse.projection_span_dense A)
    rintro a ⟨p, rfl⟩
    change Φ (f p.val) = Ψ p.val
    rw [hΦ, hΨ, hψp, hf]
  have he' : φ ∘ f = ψ := by
    funext a
    have hh := congrArg (fun K : A →L[ℂ] ℂ => K a) he
    change Φ (f a) = Ψ a at hh
    change φ (f a) = ψ a
    simpa only [hΦ, hΨ] using hh
  rw [he']
  exact hψ

theorem exists_normal_star_lift (h : FrameHom (ProjAlg A) (ProjAlg B)) :
    ∃ f : A →⋆ₐ[ℂ] B, IsNormalStarHom f ∧ ∀ p : ProjAlg A, f p.val = (h p).val := by
  obtain ⟨f, hf⟩ := exists_starAlgHom_lift (frameBooleanHom h)
  exact ⟨f, star_lift_normal h f hf, hf⟩

instance projectionFunctor_full : projectionFunctor.{u}.Full where
  map_surjective := by
    intro A B f
    obtain ⟨g, hg, hgp⟩ := exists_normal_star_lift (MLoc.frameHom f)
    refine ⟨(show B.unop ⟶ A.unop from ⟨g, hg⟩).op, ?_⟩
    apply InducedCategory.hom_ext
    apply Quiver.Hom.unop_inj
    apply Frm.hom_ext
    apply FrameHom.ext
    intro p
    apply Gelfand311.projection_ext
    exact hgp p

end
end Gelfand320
end Gelfand320WholeSource53

/- Source module Work.Gelfand320.EquivalenceAssembly; SHA256 c37bc09d94de83c671d0fcae2b105bb450584d58fa4490a5f0f35160ed2d3403. -/
section Gelfand320WholeSource54

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory Opposite GelfandVNA.Duality

namespace Gelfand320
universe u

/-- Once the projection object construction is essentially surjective, the
checked full and faithful projection functor supplies the exact equivalence
and its required canonical projection action. -/
theorem equivalence_of_projection_objects
    (hobjects : ∀ B : MLoc.{u}, ∃ A : CVNA.{u}, Nonempty (B.carrier ≃o ProjAlg A.carrier)) :
    ∃ e : MLoc.{u} ≌ CVNA.{u}ᵒᵖ,
      ∃ ι : ∀ A : CVNA.{u}, (e.inverse.obj (op A)).carrier ≃o ProjAlg A.carrier,
        ∀ {A B : CVNA.{u}} (f : A ⟶ B) (p : (e.inverse.obj (op A)).carrier),
          (ι B (MLoc.frameHom (e.inverse.map f.op) p)).val = f.1 (ι A p).val := by
  letI : projectionFunctor.{u}.EssSurj := ⟨fun B => by
    obtain ⟨A, ⟨h⟩⟩ := hobjects B
    exact ⟨op A, ⟨InducedCategory.isoMk (Frm.Iso.mk h).op⟩⟩⟩
  letI : projectionFunctor.{u}.IsEquivalence := {}
  refine ⟨projectionFunctor.asEquivalence.symm, fun _ => OrderIso.refl _, ?_⟩
  intro A B f p
  exact projectionFunctor_map f p

end Gelfand320
end
end Gelfand320WholeSource54

/- Source module Work.Gelfand320.ObjectAssembly; SHA256 45a795c04e9176f9da2a1afacefbe8a08926eb69171c7b66d6c6d0fce55ca9a5. -/
section Gelfand320WholeSource55

set_option autoImplicit false
noncomputable section
open CategoryTheory Opposite GelfandVNA.Duality

namespace Gelfand320
universe u

/-- The Stone algebra of a localizable Boolean algebra, equipped with its
constructed Banach predual, is an actual object of the canonical category. -/
def stepObject (B : MLoc.{u}) : CVNA.{u} where
  carrier := StepAlgebra B.carrier
  comm := inferInstance
  wstar := stepWStarAlgebra (MLocObj.localizable B)

/-- Every localizable Boolean algebra is the projection algebra of its
Stone algebra with the constructed predual. -/
theorem exists_projection_object (B : MLoc.{u}) :
    ∃ A : CVNA.{u}, Nonempty (B.carrier ≃o ProjAlg A.carrier) :=
  ⟨stepObject B, ⟨booleanProjectionIso B.carrier⟩⟩

end Gelfand320

universe u

/-- The exact canonical duality, with the prescribed action on projections. -/
theorem solution :
    ∃ e : MLoc.{u} ≌ CVNA.{u}ᵒᵖ,
      ∃ ι : ∀ A : CVNA.{u}, (e.inverse.obj (op A)).carrier ≃o ProjAlg A.carrier,
        ∀ {A B : CVNA.{u}} (f : A ⟶ B) (p : (e.inverse.obj (op A)).carrier),
          (ι B (MLoc.frameHom (e.inverse.map f.op) p)).val = f.1 (ι A p).val := by
  exact Gelfand320.equivalence_of_projection_objects Gelfand320.exists_projection_object
end
end Gelfand320WholeSource55
