-- Prove2me | solution 1 for FullGroupCStar.exists_starAlgHom_comp_of_eq_and_range_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T09:27:29.042472+00:00
-- url     : https://prove2.me/submissions/d8a91dbd-c02e-4324-85be-eb841f9769eb

import Definitions.Def_FullGroupCStar
import Mathlib

universe u v

section
section
/-!
# Every unitary representation, in any universe, extends to `C*(G)`

`FullGroupCStar.exists_starAlgHom_comp_of_eq_and_range_eq`.

* The norm bound `‖ρ(x)‖ ≤ maxNorm x` for `ρ` on a Hilbert space `H` in any universe: for a vector
  `ξ`, the GNS-type space `GNS ρ ξ` (the group algebra with the seminorm `x ↦ ‖ρ(x) ξ‖`, completed)
  lives in `G`'s universe, and `G` acts on it by left multiplication; the cyclic vector `[1]` gives
  `‖ρ(x) ξ‖ = ‖π(x)[1]‖ ≤ maxNorm x · ‖ξ‖`.
* The range of a *-homomorphism of C*-algebras is closed: every `φ a` has a preimage of norm at most
  `‖φ a‖` (a functional-calculus truncation of `a`), so the induced map on `A ⧸ ker φ` is
  antilipschitz.
-/


noncomputable section

open UniformSpace

namespace FullGroupCStar.ExtAux

/-! ## The range of a *-homomorphism of C*-algebras is closed -/

section ClosedRange

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

open CStarAlgebra

/-- The truncation `t ↦ r / max r √t`, equal to `1` on `[0, r²]`. -/
def trunc (r : ℝ) (t : ℝ) : ℝ := r / max r (Real.sqrt t)

lemma continuous_trunc {r : ℝ} (hr : 0 < r) : Continuous (trunc r) :=
  continuous_const.div (continuous_const.max Real.continuous_sqrt)
    (fun t => (lt_of_lt_of_le hr (le_max_left _ _)).ne')

lemma trunc_eq_one {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) (htr : t ≤ r * r) : trunc r t = 1 := by
  have : Real.sqrt t ≤ r := by
    rw [Real.sqrt_le_left hr.le]; nlinarith
  rw [trunc, max_eq_left this, div_self hr.ne']

lemma trunc_mul_le {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    |trunc r t * t * trunc r t| ≤ r * r := by
  set m := max r (Real.sqrt t) with hm_def
  have hm : 0 < m := lt_of_lt_of_le hr (le_max_left _ _)
  have htm : t ≤ m * m := by
    have h1 : Real.sqrt t ≤ m := le_max_right _ _
    have h2 := Real.mul_self_sqrt ht
    nlinarith [Real.sqrt_nonneg t]
  have heq : trunc r t * t * trunc r t = r * r * (t / (m * m)) := by
    simp only [trunc, ← hm_def]; field_simp
  rw [heq, abs_of_nonneg (by positivity)]
  have : t / (m * m) ≤ 1 := (div_le_one (by positivity)).mpr htm
  nlinarith [mul_self_nonneg r]

/-- Every value of a *-homomorphism of C*-algebras has a preimage of no larger norm. -/
lemma exists_preimage_norm_le (φ : A →⋆ₐ[ℂ] B) (a : A) :
    ∃ a' : A, φ a' = φ a ∧ ‖a'‖ ≤ ‖φ a‖ := by
  rcases (norm_nonneg (φ a)).eq_or_lt with h0 | hr
  · refine ⟨0, ?_, by simp [← h0]⟩
    rw [map_zero, eq_comm, ← norm_eq_zero, ← h0]
  set r := ‖φ a‖ with hr_def
  set x := star a * a with hx_def
  have hxsa : IsSelfAdjoint x := .star_mul_self a
  have hcont : Continuous φ := map_continuous φ
  refine ⟨a * cfc (trunc r) x, ?_, ?_⟩
  · have hφx : φ x = star (φ a) * φ a := by rw [hx_def, map_mul, map_star]
    have hmap : φ (cfc (trunc r) x) = cfc (trunc r) (φ x) :=
      StarAlgHom.map_cfc φ (trunc r) x (continuous_trunc hr).continuousOn hcont hxsa (hxsa.map φ)
    have : Nontrivial B := nontrivial_of_ne (φ a) 0 (norm_pos_iff.mp hr)
    rw [map_mul, hmap]
    have hnn : 0 ≤ φ x := by rw [hφx]; exact star_mul_self_nonneg _
    have : cfc (trunc r) (φ x) = cfc (fun _ : ℝ => (1 : ℝ)) (φ x) := by
      refine cfc_congr fun t ht => ?_
      have ht0 : 0 ≤ t := spectrum_nonneg_of_nonneg hnn ht
      have htle : t ≤ r * r := by
        have := spectrum.norm_le_norm_of_mem ht
        rw [Real.norm_of_nonneg ht0, hφx, CStarRing.norm_star_mul_self] at this
        exact this
      exact trunc_eq_one hr ht0 htle
    rw [this, cfc_const_one ℝ (φ x), mul_one]
  · set c := cfc (trunc r) x
    have hc : IsSelfAdjoint c := cfc_predicate (trunc r) x
    have hxnn : 0 ≤ x := star_mul_self_nonneg a
    have key : star (a * c) * (a * c) = cfc (fun t => trunc r t * t * trunc r t) x := by
      rw [star_mul, hc.star_eq, mul_assoc, ← mul_assoc (star a), ← hx_def, ← mul_assoc]
      rw [cfc_mul (fun t => trunc r t * t) (trunc r) x
          ((continuous_trunc hr).continuousOn.mul continuousOn_id)
          (continuous_trunc hr).continuousOn,
        cfc_mul (trunc r) (fun t => t) x (continuous_trunc hr).continuousOn continuousOn_id,
        cfc_id' ℝ x]
    have hbound : ‖star (a * c) * (a * c)‖ ≤ r * r := by
      rw [key]
      refine norm_cfc_le (by positivity) fun t ht => ?_
      rw [Real.norm_eq_abs]
      exact trunc_mul_le hr (spectrum_nonneg_of_nonneg hxnn ht)
    rw [CStarRing.norm_star_mul_self] at hbound
    exact (mul_self_le_mul_self_iff (norm_nonneg _) hr.le).mpr hbound

/-- The range of a *-homomorphism of C*-algebras is closed. -/
lemma isClosed_range (φ : A →⋆ₐ[ℂ] B) : IsClosed (Set.range φ) := by
  have hcont : Continuous φ := map_continuous φ
  let f : A →L[ℂ] B := ⟨φ.toAlgHom.toLinearMap, hcont⟩
  let K : Submodule ℂ A := LinearMap.ker f.toLinearMap
  have : IsClosed (K : Set A) := isClosed_singleton.preimage hcont
  let g : (A ⧸ K) →ₗ[ℂ] B := K.liftQ f.toLinearMap le_rfl
  have hg_mk : ∀ a : A, g (Submodule.Quotient.mk a) = φ a := fun a => rfl
  -- `g` is bounded below and above by the norm
  have hlow : ∀ q : A ⧸ K, ‖q‖ ≤ ‖g q‖ := by
    intro q
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective K q
    obtain ⟨a', ha', hn⟩ := exists_preimage_norm_le φ a
    have : (Submodule.Quotient.mk a : A ⧸ K) = Submodule.Quotient.mk a' := by
      rw [Submodule.Quotient.eq]
      change f (a - a') = 0
      rw [map_sub]
      change φ a - φ a' = 0
      rw [ha', sub_self]
    rw [this, hg_mk, ha']
    exact (Submodule.Quotient.norm_mk_le K a').trans hn
  have hup : ∀ q : A ⧸ K, ‖g q‖ ≤ 1 * ‖q‖ := by
    intro q
    rw [one_mul]
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨a, ha, hlt⟩ := QuotientAddGroup.exists_norm_mk_lt (S := K.toAddSubgroup) q hε
    have : g q = φ a := by rw [← ha]; rfl
    rw [this]
    exact (NonUnitalStarAlgHom.norm_apply_le φ a).trans_lt hlt
  let gc : (A ⧸ K) →L[ℂ] B := g.mkContinuous 1 hup
  have hanti : AntilipschitzWith 1 gc := by
    refine AntilipschitzWith.of_le_mul_dist fun q₁ q₂ => ?_
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, NNReal.coe_one, one_mul]
    exact hlow _
  have hrange : Set.range gc = Set.range φ := by
    ext b
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective K q
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨Submodule.Quotient.mk a, rfl⟩
  rw [← hrange]
  exact hanti.isClosed_range gc.uniformContinuous

end ClosedRange

/-! ## Representations in any universe, extended to `ℂ[G]` -/

variable {G : Type u} [Group G] {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- `ρ` extended linearly to the group algebra. -/
def ext (ρ : G →* unitary (H →L[ℂ] H)) : MonoidAlgebra ℂ G →ₐ[ℂ] (H →L[ℂ] H) :=
  MonoidAlgebra.lift ℂ _ G ((unitary (H →L[ℂ] H)).subtype.comp ρ)

variable (ρ : G →* unitary (H →L[ℂ] H))

lemma ext_single (g : G) (c : ℂ) :
    ext ρ (MonoidAlgebra.single g c) = c • (ρ g : H →L[ℂ] H) :=
  MonoidAlgebra.lift_single _ _ _

lemma coe_ρ_inv (g : G) : (ρ g⁻¹ : H →L[ℂ] H) = star (ρ g : H →L[ℂ] H) := by
  rw [map_inv, ← Unitary.star_eq_inv, Unitary.coe_star]

lemma ext_starMA (x : MonoidAlgebra ℂ G) : ext ρ (starMA x) = star (ext ρ x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp [starMA_zero]
  | add x y hx hy => rw [starMA_add, map_add, map_add, star_add, hx, hy]
  | single g c =>
    rw [starMA_single, ext_single, ext_single, star_smul, coe_ρ_inv]
    rfl

/-! ## The cyclic representation generated by a vector, in `G`'s universe -/

/-- The group algebra, to carry the seminorm `x ↦ ‖ρ(x) ξ‖`. -/
def GNS (_ρ : G →* unitary (H →L[ℂ] H)) (_ξ : H) : Type u := MonoidAlgebra ℂ G

variable (ξ : H)

instance : AddCommGroup (GNS ρ ξ) := inferInstanceAs (AddCommGroup (MonoidAlgebra ℂ G))

instance : Module ℂ (GNS ρ ξ) := inferInstanceAs (Module ℂ (MonoidAlgebra ℂ G))

/-- The identity map of the group algebra into `GNS ρ ξ`. -/
def toGNS : MonoidAlgebra ℂ G →ₗ[ℂ] GNS ρ ξ := LinearMap.id

/-- `x ↦ ρ(x) ξ`. -/
def V : GNS ρ ξ →ₗ[ℂ] H :=
  (ContinuousLinearMap.apply ℂ H ξ).toLinearMap ∘ₗ (ext ρ).toLinearMap

instance : SeminormedAddCommGroup (GNS ρ ξ) := SeminormedAddCommGroup.induced _ _ (V ρ ξ)

instance : InnerProductSpace ℂ (GNS ρ ξ) := InnerProductSpace.induced (V ρ ξ)

lemma norm_toGNS (x : MonoidAlgebra ℂ G) : ‖toGNS ρ ξ x‖ = ‖ext ρ x ξ‖ := rfl

/-- Left multiplication by `g` on `GNS ρ ξ`. -/
def LmulL (g : G) : GNS ρ ξ →ₗ[ℂ] GNS ρ ξ :=
  LinearMap.mulLeft ℂ (MonoidAlgebra.single g (1 : ℂ) : MonoidAlgebra ℂ G)

lemma ext_single_one_mul (g : G) (x : MonoidAlgebra ℂ G) :
    ext ρ (MonoidAlgebra.single g 1 * x) ξ = (ρ g : H →L[ℂ] H) (ext ρ x ξ) := by
  rw [map_mul, ext_single, one_smul]; rfl

lemma norm_LmulL (g : G) (x : GNS ρ ξ) : ‖LmulL ρ ξ g x‖ = ‖x‖ := by
  change ‖toGNS ρ ξ (MonoidAlgebra.single g 1 * (show MonoidAlgebra ℂ G from x))‖ =
    ‖toGNS ρ ξ (show MonoidAlgebra ℂ G from x)‖
  rw [norm_toGNS, norm_toGNS, ext_single_one_mul, Unitary.norm_map]

/-- Left multiplication by `g` on `GNS ρ ξ`, an isometry. -/
def Lmul (g : G) : GNS ρ ξ →L[ℂ] GNS ρ ξ :=
  (LmulL ρ ξ g).mkContinuous 1 fun x => by rw [norm_LmulL, one_mul]

/-- The Hilbert space of the cyclic representation: the completion of `GNS ρ ξ`, in `Type u`. -/
abbrev Kc := Completion (GNS ρ ξ)

/-- Left multiplication by `g`, extended to the completion. -/
def U (g : G) : Kc ρ ξ →L[ℂ] Kc ρ ξ := (Lmul ρ ξ g).completion

lemma U_coe (g : G) (x : GNS ρ ξ) : U ρ ξ g (x : Kc ρ ξ) = ((LmulL ρ ξ g x : GNS ρ ξ) : Kc ρ ξ) :=
  ContinuousLinearMap.completion_apply_coe _ _

lemma norm_U (g : G) (y : Kc ρ ξ) : ‖U ρ ξ g y‖ = ‖y‖ := by
  induction y using Completion.induction_on with
  | hp => exact isClosed_eq (continuous_norm.comp (U ρ ξ g).continuous) continuous_norm
  | ih x => rw [U_coe, Completion.norm_coe, Completion.norm_coe, norm_LmulL]

lemma U_one : U ρ ξ 1 = 1 := by
  ext y
  induction y using Completion.induction_on with
  | hp => exact isClosed_eq (U ρ ξ 1).continuous continuous_id
  | ih x =>
    rw [U_coe, ContinuousLinearMap.one_apply]
    congr 1
    change (MonoidAlgebra.single (1 : G) (1 : ℂ) * (show MonoidAlgebra ℂ G from x)) = x
    rw [← MonoidAlgebra.one_def, one_mul]

lemma U_mul (g h : G) : U ρ ξ (g * h) = U ρ ξ g * U ρ ξ h := by
  ext y
  induction y using Completion.induction_on with
  | hp => exact isClosed_eq (U ρ ξ _).continuous ((U ρ ξ g).continuous.comp (U ρ ξ h).continuous)
  | ih x =>
    rw [ContinuousLinearMap.mul_apply, U_coe, U_coe, U_coe]
    congr 1
    change (MonoidAlgebra.single (g * h) (1 : ℂ) * (show MonoidAlgebra ℂ G from x)) =
      MonoidAlgebra.single g (1 : ℂ) *
        (MonoidAlgebra.single h (1 : ℂ) * (show MonoidAlgebra ℂ G from x))
    rw [← mul_assoc, MonoidAlgebra.single_mul_single, one_mul]

/-- `g ↦ U g` as a monoid homomorphism. -/
def Umon : G →* (Kc ρ ξ →L[ℂ] Kc ρ ξ) where
  toFun := U ρ ξ
  map_one' := U_one ρ ξ
  map_mul' := U_mul ρ ξ

lemma Umon_mem (g : G) : Umon ρ ξ g ∈ unitary (Kc ρ ξ →L[ℂ] Kc ρ ξ) := by
  let e' : (Kc ρ ξ →L[ℂ] Kc ρ ξ)ˣ :=
    { val := Umon ρ ξ g
      inv := Umon ρ ξ g⁻¹
      val_inv := by rw [← map_mul, mul_inv_cancel, map_one]
      inv_val := by rw [← map_mul, inv_mul_cancel, map_one] }
  exact IsUnit.mem_unitary_of_star_mul_self ⟨e', rfl⟩
    ((Umon ρ ξ g).norm_map_iff_adjoint_comp_self.mp (norm_U ρ ξ g))

/-- The cyclic representation, a `Rep G` (its space is in `G`'s universe). -/
def rep : Rep G where
  H := Kc ρ ξ
  ρ := (Umon ρ ξ).codRestrict _ (Umon_mem ρ ξ)

/-- The class of `y` in the space of `rep ρ ξ`. -/
def mkK (y : MonoidAlgebra ℂ G) : (rep ρ ξ).H := (toGNS ρ ξ y : Kc ρ ξ)

lemma norm_mkK (y : MonoidAlgebra ℂ G) : ‖mkK ρ ξ y‖ = ‖ext ρ y ξ‖ :=
  Completion.norm_coe (toGNS ρ ξ y)

lemma rep_extend_mkK (x y : MonoidAlgebra ℂ G) :
    (rep ρ ξ).extend x (mkK ρ ξ y) = mkK ρ ξ (x * y) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero =>
    rw [map_zero, ContinuousLinearMap.zero_apply, zero_mul]
    change (0 : Kc ρ ξ) = ((0 : GNS ρ ξ) : Kc ρ ξ)
    rw [Completion.coe_zero]
  | add x x' hx hx' =>
    rw [map_add, ContinuousLinearMap.add_apply, hx, hx', add_mul]
    change ((toGNS ρ ξ _ : GNS ρ ξ) : Kc ρ ξ) + ((toGNS ρ ξ _ : GNS ρ ξ) : Kc ρ ξ) =
      ((toGNS ρ ξ (x * y + x' * y) : GNS ρ ξ) : Kc ρ ξ)
    rw [← Completion.coe_add, map_add]
  | single g c =>
    rw [Rep.extend_single, ContinuousLinearMap.smul_apply]
    change c • U ρ ξ g (toGNS ρ ξ y : Kc ρ ξ) = ((toGNS ρ ξ _ : GNS ρ ξ) : Kc ρ ξ)
    rw [U_coe, ← Completion.coe_smul]
    congr 1
    change c • (MonoidAlgebra.single g (1 : ℂ) * y) = MonoidAlgebra.single g c * y
    rw [← smul_mul_assoc, MonoidAlgebra.smul_single', mul_one]

/-- The key estimate: `‖ρ(x) ξ‖ ≤ maxNorm x · ‖ξ‖`. -/
lemma norm_ext_apply_le (x : MonoidAlgebra ℂ G) : ‖ext ρ x ξ‖ ≤ maxNorm x * ‖ξ‖ := by
  have h1 : ‖ext ρ x ξ‖ = ‖(rep ρ ξ).extend x (mkK ρ ξ 1)‖ := by
    rw [rep_extend_mkK, mul_one, norm_mkK]
  have h2 : ‖mkK ρ ξ 1‖ = ‖ξ‖ := by
    rw [norm_mkK, map_one, ContinuousLinearMap.one_apply]
  rw [h1]
  calc _ ≤ ‖(rep ρ ξ).extend x‖ * ‖mkK ρ ξ 1‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ maxNorm x * ‖ξ‖ := by
      rw [h2]; exact mul_le_mul_of_nonneg_right (norm_extend_le_maxNorm _ x) (norm_nonneg _)

omit ξ in
lemma norm_ext_le (x : MonoidAlgebra ℂ G) : ‖ext ρ x‖ ≤ maxNorm x :=
  ContinuousLinearMap.opNorm_le_bound _ (maxNorm_nonneg x) fun ξ => norm_ext_apply_le ρ ξ x

/-! ## The extension to `C*(G)` -/

/-- `ρ` on `PreAlg G`, as a ring homomorphism. -/
def extPre : PreAlg G →+* (H →L[ℂ] H) := (ext ρ).toRingHom.comp PreAlg.equiv.toAlgHom.toRingHom

lemma extPre_apply (a : PreAlg G) : extPre ρ a = ext ρ (PreAlg.equiv a) := rfl

lemma continuous_extPre : Continuous (extPre ρ) :=
  AddMonoidHomClass.continuous_of_bound (extPre ρ) 1 fun a => by
    rw [one_mul]; exact norm_ext_le ρ _

/-- The extension of `ρ` to a unital *-homomorphism `C*(G) → B(H)`. -/
def liftAny : FullGroupCStar G →⋆ₐ[ℂ] (H →L[ℂ] H) where
  __ := Completion.extensionHom (extPre ρ) (continuous_extPre ρ)
  commutes' r := by
    change Completion.extensionHom (extPre ρ) (continuous_extPre ρ)
      ((algebraMap ℂ (PreAlg G) r : PreAlg G) : FullGroupCStar G) = _
    rw [Completion.extensionHom_coe]
    exact (ext ρ).commutes r
  map_star' x := by
    have hc : Continuous (Completion.extensionHom (extPre ρ) (continuous_extPre ρ)) :=
      Completion.continuous_extension
    induction x using Completion.induction_on with
    | hp => exact isClosed_eq (hc.comp continuous_star) (continuous_star.comp hc)
    | ih a =>
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
        MonoidHom.coe_coe]
      rw [star_coe, Completion.extensionHom_coe, Completion.extensionHom_coe,
        extPre_apply, extPre_apply, PreAlg.equiv_star, ext_starMA]

lemma liftAny_coe (a : PreAlg G) :
    liftAny ρ (a : FullGroupCStar G) = ext ρ (PreAlg.equiv a) :=
  Completion.extensionHom_coe (extPre ρ) (continuous_extPre ρ) a

lemma liftAny_of (g : G) : liftAny ρ (of g) = ρ g := by
  rw [coe_of, ofHom_apply, liftAny_coe]
  change ext ρ (MonoidAlgebra.single g 1) = _
  rw [ext_single, one_smul]

lemma continuous_liftAny : Continuous (liftAny ρ) := Completion.continuous_extension

lemma ext_mem_adjoin (x : MonoidAlgebra ℂ G) :
    ext ρ x ∈ StarAlgebra.adjoin ℂ (Set.range fun g : G => (ρ g : H →L[ℂ] H)) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => rw [map_zero]; exact zero_mem _
  | add x y hx hy => rw [map_add]; exact add_mem hx hy
  | single g c =>
    rw [ext_single]
    exact SMulMemClass.smul_mem c (StarAlgebra.subset_adjoin ℂ (Set.range fun g : G => (ρ g : H →L[ℂ] H)) ⟨g, rfl⟩)

lemma liftAny_range :
    (liftAny ρ).range =
      (StarAlgebra.adjoin ℂ (Set.range fun g : G => (ρ g : H →L[ℂ] H))).topologicalClosure := by
  set S := StarAlgebra.adjoin ℂ (Set.range fun g : G => (ρ g : H →L[ℂ] H))
  apply le_antisymm
  · rintro T ⟨a, rfl⟩
    induction a using Completion.induction_on with
    | hp => exact (S.isClosed_topologicalClosure).preimage (continuous_liftAny ρ)
    | ih a =>
      change liftAny ρ (a : FullGroupCStar G) ∈ S.topologicalClosure
      rw [liftAny_coe]
      exact S.le_topologicalClosure (ext_mem_adjoin ρ _)
  · refine StarSubalgebra.topologicalClosure_minimal ?_ ?_
    · refine StarAlgebra.adjoin_le ?_
      rintro _ ⟨g, rfl⟩
      exact ⟨(of g : FullGroupCStar G), liftAny_of ρ g⟩
    · exact isClosed_range (liftAny ρ)

end FullGroupCStar.ExtAux

namespace FullGroupCStar

theorem exists_starAlgHom_comp_of_eq_and_range_eq_dev {G : Type u} [Group G] (H : Type v)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ : G →* unitary (H →L[ℂ] H)) :
    ∃ φ : FullGroupCStar G →⋆ₐ[ℂ] (H →L[ℂ] H), (∀ g : G, φ (of g) = ρ g) ∧
      φ.range = (StarAlgebra.adjoin ℂ (Set.range fun g : G => (ρ g : H →L[ℂ] H))).topologicalClosure :=
  ⟨ExtAux.liftAny ρ, ExtAux.liftAny_of ρ, ExtAux.liftAny_range ρ⟩

end FullGroupCStar

end
end
end

section
open FullGroupCStar

theorem solution {G : Type u} [Group G] (H : Type v)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ : G →* unitary (H →L[ℂ] H)) :
    ∃ φ : FullGroupCStar G →⋆ₐ[ℂ] (H →L[ℂ] H), (∀ g : G, φ (of g) = ρ g) ∧
      φ.range = (StarAlgebra.adjoin ℂ (Set.range fun g : G => (ρ g : H →L[ℂ] H))).topologicalClosure := by
  apply FullGroupCStar.exists_starAlgHom_comp_of_eq_and_range_eq_dev <;> assumption

end
