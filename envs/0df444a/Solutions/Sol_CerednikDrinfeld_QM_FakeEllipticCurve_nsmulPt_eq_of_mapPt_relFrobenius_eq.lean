-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.nsmulPt_eq_of_mapPt_relFrobenius_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/200d365d-f30e-5d57-a47a-6f40e21b3671

import Mathlib
import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_SchemeFrobenius
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_nsmulPt_eq_of_mapPt_relFrobenius_eq

set_option autoImplicit false

universe u

namespace RelVersch

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

noncomputable section

section CT
open PiTensorProduct
open scoped TensorProduct

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (D : Type u) [CommRing D] [Algebra k D]

abbrev TP : Type u := PiTensorProduct k (fun _ : ZMod p => D)

noncomputable def rot : TP k p D →ₐ[k] TP k p D :=
  PiTensorProduct.liftAlgHom ((PiTensorProduct.tprod k).domDomCongr (Equiv.addRight (1 : ZMod p)))
    rfl
    (fun x y => by
      simp only [MultilinearMap.domDomCongr_apply, Pi.mul_apply]
      rw [PiTensorProduct.mul_def, PiTensorProduct.mul_tprod_tprod]
      rfl)

theorem rot_tprod (v : ZMod p → D) :
    rot k p D (PiTensorProduct.tprod k v) = PiTensorProduct.tprod k (fun i => v (i + 1)) := by
  rw [rot, PiTensorProduct.liftAlgHom_apply, PiTensorProduct.lift.tprod, MultilinearMap.domDomCongr_apply]
  rfl

noncomputable def nabla : TP k p D →ₐ[k] D :=
  PiTensorProduct.liftAlgHom (MultilinearMap.mkPiAlgebra k (ZMod p) D)
    (by simp) (fun x y => by simp [Finset.prod_mul_distrib])

theorem nabla_tprod (v : ZMod p → D) : nabla k p D (PiTensorProduct.tprod k v) = ∏ i, v i := by
  rw [nabla, PiTensorProduct.liftAlgHom_apply, PiTensorProduct.lift.tprod, MultilinearMap.mkPiAlgebra_apply]

theorem rot_singleAlgHom (i : ZMod p) (d : D) :
    rot k p D (PiTensorProduct.singleAlgHom (R := k) (A := fun _ : ZMod p => D) i d) = PiTensorProduct.singleAlgHom (R := k) (A := fun _ : ZMod p => D) (i - 1) d := by
  classical
  rw [PiTensorProduct.singleAlgHom_apply, PiTensorProduct.singleAlgHom_apply, rot_tprod]
  congr 1
  funext j
  simp only [MonoidHom.mulSingle_apply, Pi.mulSingle_apply]
  by_cases h : j = i - 1
  · subst h; simp
  · rw [if_neg h, if_neg (fun h' => h (by rw [← h', add_sub_cancel_right]))]

theorem nabla_singleAlgHom (i : ZMod p) (d : D) : nabla k p D (PiTensorProduct.singleAlgHom (R := k) (A := fun _ : ZMod p => D) i d) = d := by
  classical
  rw [PiTensorProduct.singleAlgHom_apply, nabla_tprod]
  simp

def sh {κ : Type u} (f : ZMod p → κ) : ZMod p → κ := fun i => f (i + 1)

def shBy {κ : Type u} (m : ZMod p) (f : ZMod p → κ) : ZMod p → κ := fun i => f (i + m)

theorem shBy_zero {κ : Type u} (f : ZMod p → κ) : shBy p 0 f = f := by
  funext i; simp [shBy]

theorem sh_shBy {κ : Type u} (m : ZMod p) (f : ZMod p → κ) : sh p (shBy p m f) = shBy p (m + 1) f := by
  funext i; simp only [sh, shBy]; congr 1; ring

theorem shBy_natCast_succ {κ : Type u} (n : ℕ) (f : ZMod p → κ) :
    shBy p ((n + 1 : ℕ) : ZMod p) f = sh p (shBy p (n : ZMod p) f) := by
  rw [sh_shBy, Nat.cast_succ]

theorem shBy_induction {κ : Type u} (P : (ZMod p → κ) → Prop) (hP : ∀ f, P f → P (sh p f)) (f : ZMod p → κ) (hf : P f)
    (m : ZMod p) : P (shBy p m f) := by
  have : ∀ n : ℕ, P (shBy p (n : ZMod p) f) := by
    intro n
    induction n with
    | zero => rw [Nat.cast_zero, shBy_zero]; exact hf
    | succ n ih => rw [shBy_natCast_succ]; exact hP _ ih
  simpa using this m.val

theorem shBy_injective {κ : Type u} (f : ZMod p → κ) (hf : ¬ ∀ i, f i = f 0) :
    Function.Injective (fun m : ZMod p => shBy p m f) := by
  intro k l hkl
  by_contra hne
  apply hf
  have h1 : ∀ i, f (i + (k - l)) = f i := by
    intro i
    have := congr_fun hkl (i - l)
    simp only [shBy] at this
    rw [sub_add_cancel] at this
    rw [← this]; congr 1; ring
  have hm : (k - l : ZMod p) ≠ 0 := sub_ne_zero.2 hne
  have h2 : ∀ (n : ℕ) (i : ZMod p), f (i + n • (k - l)) = f i := by
    intro n
    induction n with
    | zero => intro i; simp
    | succ n ih => intro i; rw [succ_nsmul, ← add_assoc, h1, ih]
  intro i

  have hi : i = 0 + ((i / (k - l)).val) • (k - l) := by
    rw [zero_add, ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val, smul_eq_mul, div_mul_cancel₀ i hm]
  rw [hi, h2]

theorem sum_eq_zero_of_sh_stable {κ : Type u} {M : Type u} [AddCommGroup M] [Module k M]
    (t : (ZMod p → κ) → M) (ht : ∀ f, t (sh p f) = t f) :
    ∀ (S : Finset (ZMod p → κ)), (∀ f ∈ S, sh p f ∈ S) → (∀ f ∈ S, ¬ ∀ i, f i = f 0) → ∑ f ∈ S, t f = 0 := by
  classical
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro hstab hnc
    rcases S.eq_empty_or_nonempty with hS | ⟨f₀, hf₀⟩
    · rw [hS, Finset.sum_empty]

    let O : Finset (ZMod p → κ) := Finset.image (fun m : ZMod p => shBy p m f₀) Finset.univ
    have hOS : O ⊆ S := by
      intro f hf
      rw [Finset.mem_image] at hf
      obtain ⟨m, -, rfl⟩ := hf
      exact shBy_induction p (fun g => g ∈ S) (fun g hg => hstab g hg) f₀ hf₀ m
    have htO : ∀ m : ZMod p, t (shBy p m f₀) = t f₀ :=
      fun m => shBy_induction p (fun g => t g = t f₀) (fun g hg => (ht g).trans hg) f₀ rfl m
    have hsumO : ∑ f ∈ O, t f = 0 := by
      rw [Finset.sum_image (fun k _ l _ hkl => shBy_injective p f₀ (hnc f₀ hf₀) hkl)]
      simp only [htO, Finset.sum_const, Finset.card_univ]
      rw [ZMod.card, ← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero k p, zero_smul]
    have hO_ne : O.Nonempty := ⟨shBy p 0 f₀, Finset.mem_image.2 ⟨0, Finset.mem_univ _, rfl⟩⟩
    have hlt : S \ O ⊂ S := Finset.sdiff_ssubset hOS hO_ne
    have hstab' : ∀ f ∈ S \ O, sh p f ∈ S \ O := by
      intro f hf
      rw [Finset.mem_sdiff] at hf ⊢
      refine ⟨hstab f hf.1, fun hmem => hf.2 ?_⟩
      rw [Finset.mem_image] at hmem ⊢
      obtain ⟨m, -, hm⟩ := hmem
      refine ⟨m - 1, Finset.mem_univ _, ?_⟩
      funext i
      have := congr_fun hm (i - 1)
      simp only [sh, shBy, sub_add_cancel] at this
      simp only [shBy]
      rw [← this]; congr 1; ring
    have hnc' : ∀ f ∈ S \ O, ¬ ∀ i, f i = f 0 := fun f hf => hnc f (Finset.mem_sdiff.1 hf).1
    rw [← Finset.sum_sdiff hOS, ih _ hlt hstab' hnc', hsumO, add_zero]

theorem nabla_mem_bot_of_rot_eq (hD : ∀ d : D, d ^ p ∈ (⊥ : Subalgebra k D))
    (w : TP k p D) (hw : rot k p D w = w) : nabla k p D w ∈ (⊥ : Subalgebra k D) := by
  classical
  let b := Module.Free.chooseBasis k D
  let Bs : Module.Basis (ZMod p → Module.Free.ChooseBasisIndex k D) k (TP k p D) :=
    Basis.piTensorProduct (fun _ : ZMod p => b)

  have hrepr : ∀ v : TP k p D, Bs.repr (rot k p D v) = Finsupp.mapDomain (sh p) (Bs.repr v) := by
    intro v
    have key : Bs.repr.toLinearMap ∘ₗ (rot k p D).toLinearMap =
        (Finsupp.lmapDomain k k (sh p)) ∘ₗ Bs.repr.toLinearMap := by
      apply Bs.ext
      intro g
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearEquiv.coe_coe, Finsupp.lmapDomain_apply,
        Module.Basis.repr_self, Finsupp.mapDomain_single]
      have : rot k p D (Bs g) = Bs (sh p g) := by
        simp only [Bs, Basis.piTensorProduct_apply, rot_tprod]
        rfl
      rw [this, Module.Basis.repr_self]
    exact DFunLike.congr_fun key v
  set c := Bs.repr w with hc
  have hcsh : ∀ g, c (sh p g) = c g := by
    intro g
    have h1 : c = Finsupp.mapDomain (sh p) c := by rw [hc, ← hrepr, hw]
    conv_lhs => rw [h1]
    exact Finsupp.mapDomain_apply (fun g₁ g₂ h => by
      funext i; have := congr_fun h (i - 1); simpa [sh] using this) c g

  let β : (ZMod p → Module.Free.ChooseBasisIndex k D) → D := fun g => ∏ i, b (g i)
  have hβsh : ∀ g, β (sh p g) = β g := by
    intro g
    exact Fintype.prod_equiv (Equiv.addRight (1 : ZMod p)) _ _ (fun i => rfl)
  have hnablaB : ∀ g, nabla k p D (Bs g) = β g := by
    intro g
    simp only [Bs, Basis.piTensorProduct_apply, nabla_tprod, β]
  have hw' : nabla k p D w = ∑ g ∈ c.support, c g • β g := by
    conv_lhs => rw [← Bs.linearCombination_repr w, Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_smul, hnablaB]
  rw [hw']

  rw [← Finset.sum_filter_add_sum_filter_not c.support (fun g => ∀ i, g i = g 0)]
  refine Subalgebra.add_mem _ (Subalgebra.sum_mem _ fun g hg => ?_) ?_
  ·
    rw [Finset.mem_filter] at hg
    refine Subalgebra.smul_mem _ ?_ _
    have : β g = b (g 0) ^ p := by
      simp only [β]
      rw [Finset.prod_congr rfl (fun i _ => by rw [hg.2 i]), Finset.prod_const, Finset.card_univ, ZMod.card]
    rw [this]; exact hD _
  ·
    have h0 := sum_eq_zero_of_sh_stable k p (fun g => c g • β g) (fun g => by simp only [hcsh, hβsh])
      (c.support.filter fun g => ¬ ∀ i, g i = g 0)
      (fun g hg => by
        rw [Finset.mem_filter, Finsupp.mem_support_iff] at hg ⊢
        refine ⟨by rw [hcsh]; exact hg.1, fun hsh => hg.2 ?_⟩
        intro i
        have h1 := hsh (i - 1)
        have h2 := hsh (0 - 1)
        simp only [sh, sub_add_cancel, zero_sub] at h1 h2
        rw [h1, ← h2, neg_add_cancel])
      (fun g hg => (Finset.mem_filter.1 hg).2)
    rw [h0]; exact Subalgebra.zero_mem _

end CT

section Points

open AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

abbrev sOf (B : Type u) [CommRing B] [Algebra k B] : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k B))

abbrev Pts (B : Type u) [CommRing B] [Algebra k B] : Type u := SchemeHomOver (sOf k B) f

omit hp in
theorem specMap_algHom_comp_sOf {B₁ B₂ : Type u} [CommRing B₁] [Algebra k B₁] [CommRing B₂] [Algebra k B₂] (φ : B₁ →ₐ[k] B₂) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ sOf k B₁ = sOf k B₂ := by
  rw [sOf, sOf, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext φ.comp_algebraMap

variable {k f}

def Gmap {B₁ B₂ : Type u} [CommRing B₁] [Algebra k B₁] [CommRing B₂] [Algebra k B₂]
    (φ : B₁ →ₐ[k] B₂) (x : Pts k f B₁) : Pts k f B₂ :=
  GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom φ.toRingHom)) (specMap_algHom_comp_sOf k φ) x

omit hp in
theorem Gmap_coe {B₁ B₂ : Type u} [CommRing B₁] [Algebra k B₁] [CommRing B₂] [Algebra k B₂]
    (φ : B₁ →ₐ[k] B₂) (x : Pts k f B₁) : (Gmap φ x).1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ x.1 := rfl

omit hp in
theorem Gmap_comp {B₁ B₂ B₃ : Type u} [CommRing B₁] [Algebra k B₁] [CommRing B₂] [Algebra k B₂]
    [CommRing B₃] [Algebra k B₃] (φ : B₁ →ₐ[k] B₂) (ψ : B₂ →ₐ[k] B₃) (x : Pts k f B₁) :
    Gmap ψ (Gmap φ x) = Gmap (ψ.comp φ) x := by
  apply Subtype.ext
  rw [Gmap_coe, Gmap_coe, Gmap_coe, ← Category.assoc, ← Spec.map_comp]
  rfl

omit hp in
theorem Gmap_id {B : Type u} [CommRing B] [Algebra k B] (x : Pts k f B) : Gmap (AlgHom.id k B) x = x := by
  apply Subtype.ext
  rw [Gmap_coe]
  change Spec.map (𝟙 (CommRingCat.of B)) ≫ x.1 = x.1
  rw [Spec.map_id, Category.id_comp]

omit hp in
theorem Gmap_congr {B₁ B₂ : Type u} [CommRing B₁] [Algebra k B₁] [CommRing B₂] [Algebra k B₂]
    {φ ψ : B₁ →ₐ[k] B₂} (h : φ = ψ) (x : Pts k f B₁) : Gmap φ x = Gmap ψ x := by subst h; rfl

variable (L : RelativeGroupLaw k f)

omit hp in
theorem Gmap_mul {B₁ B₂ : Type u} [CommRing B₁] [Algebra k B₁] [CommRing B₂] [Algebra k B₂]
    (φ : B₁ →ₐ[k] B₂) (x y : Pts k f B₁) : Gmap φ (L.mul _ x y) = L.mul _ (Gmap φ x) (Gmap φ y) :=
  L.mul_natural _ _ _ _ x y

omit hp in
theorem Gmap_one {B₁ B₂ : Type u} [CommRing B₁] [Algebra k B₁] [CommRing B₂] [Algebra k B₂]
    (φ : B₁ →ₐ[k] B₂) : Gmap φ (L.one (sOf k B₁)) = L.one (sOf k B₂) :=
  L.one_natural _ _ _ _

omit hp in
theorem Gmap_nsmul {B₁ B₂ : Type u} [CommRing B₁] [Algebra k B₁] [CommRing B₂] [Algebra k B₂]
    (φ : B₁ →ₐ[k] B₂) (n : ℕ) (x : Pts k f B₁) : Gmap φ (L.nsmul _ n x) = L.nsmul _ n (Gmap φ x) :=
  L.nsmul_natural _ _ _ _ n x

omit hp in

theorem comp_schemeNsmul {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x : SchemeHomOver t f) (n : ℕ) :
    x.1 ≫ L.schemeNsmul n = (L.nsmul t n x).1 := by
  have h := L.nsmul_natural f t x.1 x.2 n RelativeGroupLaw.idPoint
  have hid : GoodReductionJacobian.schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint (f := f)) = x :=
    Subtype.ext (Category.comp_id _)
  rw [hid] at h
  rw [← h]
  rfl

end Points

section Frob

open AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]

omit hp in
theorem natCast_eq_zero_of_algebra (B : Type u) [CommRing B] [Algebra k B] : (p : B) = 0 := by
  rw [← map_natCast (algebraMap k B), CharP.cast_eq_zero k p, map_zero]

def FrobTwist (k : Type u) (p : ℕ) (B : Type u) : Type u := B

omit hp in
scoped instance FrobTwist.instCommRing (B : Type u) [CommRing B] : CommRing (FrobTwist k p B) := inferInstanceAs (CommRing B)

p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_nsmulPt_eq_of_mapPt_relFrobenius_eq.RelVersch.FrobTwist"
scoped instance FrobTwist.instAlgebra (B : Type u) [CommRing B] [Algebra k B] : Algebra k (FrobTwist k p B) :=
  ((powCharRingHom B p 1 hp.out (natCast_eq_zero_of_algebra k p B)).comp (algebraMap k B)).toAlgebra

p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_nsmulPt_eq_of_mapPt_relFrobenius_eq.RelVersch.FrobTwist"
theorem FrobTwist.algebraMap_apply (B : Type u) [CommRing B] [Algebra k B] (c : k) :
    algebraMap k (FrobTwist k p B) c = (algebraMap k B c : B) ^ p := by
  show (powCharRingHom B p 1 hp.out (natCast_eq_zero_of_algebra k p B)) (algebraMap k B c) = _
  rw [powCharRingHom_apply, pow_one]

def frobAlgHom (B : Type u) [CommRing B] [Algebra k B] : B →ₐ[k] FrobTwist k p B :=
  { toRingHom := powCharRingHom B p 1 hp.out (natCast_eq_zero_of_algebra k p B)
    commutes' := fun _ => rfl }

theorem frobAlgHom_apply (B : Type u) [CommRing B] [Algebra k B] (b : B) : (frobAlgHom k p B b : B) = b ^ p := by
  show (powCharRingHom B p 1 hp.out (natCast_eq_zero_of_algebra k p B)) b = _
  rw [powCharRingHom_apply, pow_one]

def AlgHom.frobTwist {B₁ B₂ : Type u} [CommRing B₁] [Algebra k B₁] [CommRing B₂] [Algebra k B₂] (φ : B₁ →ₐ[k] B₂) :
    FrobTwist k p B₁ →ₐ[k] FrobTwist k p B₂ :=
  { toRingHom := φ.toRingHom
    commutes' := fun c => by
      show φ (algebraMap k (FrobTwist k p B₁) c) = algebraMap k (FrobTwist k p B₂) c
      rw [FrobTwist.algebraMap_apply, FrobTwist.algebraMap_apply, map_pow, φ.commutes] }

theorem frobAlgHom_comp {B₁ B₂ : Type u} [CommRing B₁] [Algebra k B₁] [CommRing B₂] [Algebra k B₂] (φ : B₁ →ₐ[k] B₂) :
    (frobAlgHom k p B₂).comp φ = (AlgHom.frobTwist k p φ).comp (frobAlgHom k p B₁) := by
  apply AlgHom.ext; intro b
  show (frobAlgHom k p B₂ (φ b) : B₂) = φ (frobAlgHom k p B₁ b : B₁)
  rw [frobAlgHom_apply, frobAlgHom_apply, map_pow]

variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

def frobPt {B : Type u} [CommRing B] [Algebra k B] (x : Pts k f B) : Pts k f (FrobTwist k p B) :=
  Gmap (frobAlgHom k p B) x

theorem frobPt_coe (hX : (p : Γ(X, ⊤)) = 0) {B : Type u} [CommRing B] [Algebra k B] (x : Pts k f B) :
    (frobPt k p f x).1 = x.1 ≫ X.frobenius p 1 hp.out hX := by
  rw [frobPt, Gmap_coe, ← frobenius_comp x.1 p 1 hp.out (natCast_eq_zero_ΓSpec (natCast_eq_zero_of_algebra k p B)) hX,
    frobenius_Spec p 1 hp.out (natCast_eq_zero_of_algebra k p B)]
  rfl

end Frob
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_nsmulPt_eq_of_mapPt_relFrobenius_eq.RelVersch.FrobTwist"

section Chart

variable (k : Type u) [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  (L : RelativeGroupLaw k f)
  {A : Type u} [CommRing A] [Algebra k A] (ι : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion ι] (hι : ι ≫ f = sOf k A)

omit hp in

theorem algHom_self_apply {B : Type u} [Semiring B] [Algebra k B] (φ : k →ₐ[k] B) (c : k) : φ c = algebraMap k B c := by
  have := φ.commutes c
  rwa [Algebra.algebraMap_self, RingHom.id_apply] at this

omit hp in
theorem algHom_self_eq_id (φ : k →ₐ[k] k) : φ = AlgHom.id k k :=
  AlgHom.ext fun c => by rw [algHom_self_apply k φ c, Algebra.algebraMap_self, RingHom.id_apply, AlgHom.id_apply]

def pt {B : Type u} [CommRing B] [Algebra k B] (χ : A →ₐ[k] B) : Pts k f B :=
  ⟨Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ ι, by rw [Category.assoc, hι]; exact specMap_algHom_comp_sOf k χ⟩

omit hp [IsOpenImmersion ι] in
theorem pt_coe {B : Type u} [CommRing B] [Algebra k B] (χ : A →ₐ[k] B) :
    (pt k ι hι χ (f := f)).1 = Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ ι := rfl

omit hp [IsOpenImmersion ι] in
theorem Gmap_pt {B₁ B₂ : Type u} [CommRing B₁] [Algebra k B₁] [CommRing B₂] [Algebra k B₂]
    (φ : B₁ →ₐ[k] B₂) (χ : A →ₐ[k] B₁) : Gmap φ (pt k ι hι χ (f := f)) = pt k ι hι (φ.comp χ) := by
  apply Subtype.ext
  rw [Gmap_coe, pt_coe, pt_coe, ← Category.assoc, ← Spec.map_comp]
  rfl

omit hp in
theorem pt_injective {B : Type u} [CommRing B] [Algebra k B] {χ₁ χ₂ : A →ₐ[k] B}
    (h : pt k ι hι χ₁ (f := f) = pt k ι hι χ₂) : χ₁ = χ₂ := by
  have h1 := congrArg Subtype.val h
  rw [pt_coe, pt_coe, cancel_mono] at h1
  have h2 := Spec.map_injective h1
  apply AlgHom.ext; intro a
  exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom h2) a

noncomputable def ρ {B : Type u} [CommRing B] [Algebra k B] (x : Pts k f B)
    (hx : Set.range x.1 ⊆ Set.range ι) : A →ₐ[k] B :=
  { toRingHom := (Spec.preimage (IsOpenImmersion.lift ι x.1 hx)).hom
    commutes' := fun c => by
      have h1 : Spec.map (Spec.preimage (IsOpenImmersion.lift ι x.1 hx)) ≫ sOf k A = sOf k B := by
        rw [Spec.map_preimage, ← hι, ← Category.assoc, IsOpenImmersion.lift_fac]; exact x.2
      have h1' : Spec.map (CommRingCat.ofHom (algebraMap k A) ≫ Spec.preimage (IsOpenImmersion.lift ι x.1 hx)) =
          Spec.map (CommRingCat.ofHom (algebraMap k B)) := by
        rw [Spec.map_comp]; exact h1
      have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h1')
      exact RingHom.congr_fun h2 c }

theorem pt_ρ {B : Type u} [CommRing B] [Algebra k B] (x : Pts k f B) (hx : Set.range x.1 ⊆ Set.range ι) :
    pt k ι hι (ρ k ι hι x hx) = x := by
  apply Subtype.ext
  rw [pt_coe]
  show Spec.map (Spec.preimage (IsOpenImmersion.lift ι x.1 hx)) ≫ ι = x.1
  rw [Spec.map_preimage, IsOpenImmersion.lift_fac]

variable (ε : A →ₐ[k] k) (hε : pt k ι hι ε = L.one (sOf k k))

include hε in
omit hp in

theorem one_eq_pt (B : Type u) [CommRing B] [Algebra k B] :
    L.one (sOf k B) = pt k ι hι ((Algebra.ofId k B).comp ε) := by
  rw [← Gmap_pt, hε, Gmap_one]

theorem spec_frobAlgHom_apply (B : Type u) [CommRing B] [Algebra k B] (q : Spec (CommRingCat.of B)) :
    (Spec.map (CommRingCat.ofHom (frobAlgHom k p B).toRingHom)) q = q := by
  rw [Spec.map_base]
  change PrimeSpectrum.comap (frobAlgHom k p B).toRingHom q = q
  ext b
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  change (frobAlgHom k p B b : B) ∈ q.asIdeal ↔ _
  rw [frobAlgHom_apply]
  exact ⟨fun h => q.2.mem_of_pow_mem _ h, fun h => Ideal.pow_mem_of_mem _ h _ hp.out.pos⟩

include hε in

theorem range_subset_of_ker {B : Type u} [CommRing B] [Algebra k B] (z : Pts k f B)
    (hz : frobPt k p f z = L.one (sOf k (FrobTwist k p B))) : Set.range z.1 ⊆ Set.range ι := by
  rintro _ ⟨q, rfl⟩
  have h1 : z.1 q = (frobPt k p f z).1 q := by
    show _ = (Spec.map (CommRingCat.ofHom (frobAlgHom k p B).toRingHom) ≫ z.1) q
    rw [Scheme.Hom.comp_apply, spec_frobAlgHom_apply]
  rw [h1, hz, one_eq_pt k L ι hι ε hε (FrobTwist k p B), pt_coe]
  exact ⟨_, rfl⟩

include hε in

theorem ρ_pow_eq {B : Type u} [CommRing B] [Algebra k B] (z : Pts k f B)
    (hz : frobPt k p f z = L.one (sOf k (FrobTwist k p B))) (a : A) :
    (ρ k ι hι z (range_subset_of_ker k p L ι hι ε hε z hz) a) ^ p = (algebraMap k B (ε a)) ^ p := by
  have h1 : frobPt k p f (pt k ι hι (ρ k ι hι z (range_subset_of_ker k p L ι hι ε hε z hz))) =
      pt k ι hι ((Algebra.ofId k (FrobTwist k p B)).comp ε) := by
    rw [pt_ρ, hz, one_eq_pt k L ι hι ε hε]
  rw [frobPt, Gmap_pt] at h1
  have h2 := congrArg (fun χ : A →ₐ[k] FrobTwist k p B => (χ a : B)) (pt_injective k ι hι h1)
  simp only [AlgHom.comp_apply] at h2
  rw [frobAlgHom_apply] at h2
  rw [h2]
  exact FrobTwist.algebraMap_apply k p B (ε a)

end Chart
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_nsmulPt_eq_of_mapPt_relFrobenius_eq.RelVersch.FrobTwist"

section Universal

open PiTensorProduct
open scoped TensorProduct

variable (k : Type u) [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  (L : RelativeGroupLaw k f) (hc : L.IsCommutative)
  {A : Type u} [CommRing A] [Algebra k A] (ι : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion ι] (hι : ι ≫ f = sOf k A)
  (ε : A →ₐ[k] k) (hε : pt k ι hι ε = L.one (sOf k k))

def J : Ideal A := Ideal.span (Set.range fun a : A => a ^ p - algebraMap k A (ε a ^ p))

abbrev AK : Type u := A ⧸ J k p ε

omit hp in
theorem J_le_ker {B : Type u} [CommRing B] [Algebra k B] (χ : A →ₐ[k] B)
    (hχ : ∀ a, χ a ^ p = algebraMap k B (ε a) ^ p) : J k p ε ≤ RingHom.ker χ.toRingHom :=
  Ideal.span_le.2 (by
    rintro _ ⟨a, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    show χ (a ^ p - algebraMap k A (ε a ^ p)) = 0
    rw [map_sub, map_pow, hχ, χ.commutes, map_pow, sub_self])

omit hp in
theorem J_le_ker_ε : J k p ε ≤ RingHom.ker ε.toRingHom :=
  J_le_ker k p ε ε (fun a => by rw [Algebra.algebraMap_self, RingHom.id_apply])

def εK : AK k p ε →ₐ[k] k :=
  Ideal.Quotient.liftₐ (J k p ε) ε (fun a ha => J_le_ker_ε k p ε ha)

omit hp in
theorem εK_mk (a : A) : εK k p ε (Ideal.Quotient.mk (J k p ε) a) = ε a := rfl

omit hp in
theorem εK_comp_mk : (εK k p ε).comp (Ideal.Quotient.mkₐ k (J k p ε)) = ε := AlgHom.ext fun a => εK_mk k p ε a

scoped instance : Nontrivial (AK k p ε) := RingHom.domain_nontrivial (εK k p ε).toRingHom

theorem pow_p_eq (d : AK k p ε) : d ^ p = algebraMap k (AK k p ε) (εK k p ε d ^ p) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective d
  rw [εK_mk, ← map_pow]
  try exact (Ideal.Quotient.eq (I := J k p ε)).mpr (Ideal.subset_span ⟨a, rfl⟩)

def uK : Pts k f (AK k p ε) :=
  pt k ι hι (Ideal.Quotient.mkₐ k (J k p ε))

include hε in
theorem frob_uK : frobPt k p f (uK k p ι hι ε (f := f)) = L.one _ := by
  rw [uK, frobPt, Gmap_pt, one_eq_pt k L ι hι ε hε]
  congr 1
  apply AlgHom.ext; intro a
  show ((frobAlgHom k p (AK k p ε)) (Ideal.Quotient.mk (J k p ε) a) : AK k p ε) = algebraMap k (FrobTwist k p (AK k p ε)) (ε a)
  rw [frobAlgHom_apply, FrobTwist.algebraMap_apply, pow_p_eq, εK_mk, map_pow]

include hε in

theorem exists_eq_Gmap_uK {B : Type u} [CommRing B] [Algebra k B] (z : Pts k f B)
    (hz : frobPt k p f z = L.one _) : ∃ ζ' : AK k p ε →ₐ[k] B, z = Gmap ζ' (uK k p ι hι ε) := by
  have hζ := ρ_pow_eq k p L ι hι ε hε z hz
  refine ⟨Ideal.Quotient.liftₐ (J k p ε) (ρ k ι hι z (range_subset_of_ker k p L ι hι ε hε z hz))
    (fun a ha => J_le_ker k p ε _ hζ ha), ?_⟩
  rw [uK, Gmap_pt]
  conv_lhs => rw [← pt_ρ k ι hι z (range_subset_of_ker k p L ι hι ε hε z hz)]
  congr 1

omit hp in

theorem pow_eq_nsmul {B : Type u} [CommRing B] [Algebra k B] (x : Pts k f B) (n : ℕ) :
    (letI := L.pointGroup (sOf k B); x ^ n) = L.nsmul _ n x := by
  letI := L.pointGroup (sOf k B)
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, ih]; rfl

include hc hε in

theorem nsmul_uK : L.nsmul _ p (uK k p ι hι ε (f := f)) = L.one _ := by
  classical

  let ιi : ZMod p → (AK k p ε →ₐ[k] TP k p (AK k p ε)) := fun i =>
    PiTensorProduct.singleAlgHom (R := k) (A := fun _ : ZMod p => AK k p ε) i
  let τ : TP k p (AK k p ε) →ₐ[k] TP k p (AK k p ε) := rot k p (AK k p ε)
  let nab : TP k p (AK k p ε) →ₐ[k] AK k p ε := nabla k p (AK k p ε)
  letI grpC : CommGroup (Pts k f (TP k p (AK k p ε))) := { L.pointGroup (sOf k (TP k p (AK k p ε))) with mul_comm := hc _ }
  letI grpCF : CommGroup (Pts k f (FrobTwist k p (TP k p (AK k p ε)))) :=
    { L.pointGroup (sOf k (FrobTwist k p (TP k p (AK k p ε)))) with mul_comm := hc _ }
  letI grpK : CommGroup (Pts k f (AK k p ε)) := { L.pointGroup (sOf k (AK k p ε)) with mul_comm := hc _ }
  let frH : Pts k f (TP k p (AK k p ε)) →* Pts k f (FrobTwist k p (TP k p (AK k p ε))) :=
    MonoidHom.mk' (Gmap (frobAlgHom k p (TP k p (AK k p ε)))) (Gmap_mul L _)
  let τH : Pts k f (TP k p (AK k p ε)) →* Pts k f (TP k p (AK k p ε)) := MonoidHom.mk' (Gmap τ) (Gmap_mul L _)
  let w : Pts k f (TP k p (AK k p ε)) := ∏ i : ZMod p, Gmap (ιi i) (uK k p ι hι ε)

  have hw1 : frobPt k p f w = L.one _ := by
    change frH w = 1
    rw [map_prod]
    refine Finset.prod_eq_one fun i _ => ?_
    change Gmap (frobAlgHom k p (TP k p (AK k p ε))) (Gmap (ιi i) (uK k p ι hι ε)) = L.one _
    rw [Gmap_comp, frobAlgHom_comp, ← Gmap_comp]
    change Gmap (AlgHom.frobTwist k p (ιi i)) (frobPt k p f (uK k p ι hι ε)) = _
    rw [frob_uK k p L ι hι ε hε, Gmap_one]

  have hω : pt k ι hι (ρ k ι hι w (range_subset_of_ker k p L ι hι ε hε w hw1)) = w := pt_ρ k ι hι w _
  have hτ : Gmap τ w = w := by
    change τH w = w
    conv_lhs => rw [show w = ∏ i : ZMod p, Gmap (ιi i) (uK k p ι hι ε) from rfl, map_prod]
    have h1 : ∀ i, τH (Gmap (ιi i) (uK k p ι hι ε)) = Gmap (ιi (i - 1)) (uK (f := f) k p ι hι ε) := by
      intro i
      change Gmap τ (Gmap (ιi i) (uK k p ι hι ε)) = _
      rw [Gmap_comp]
      exact Gmap_congr (AlgHom.ext fun d => rot_singleAlgHom k p (AK k p ε) i d) _
    simp only [h1]
    exact Fintype.prod_equiv (Equiv.subRight (1 : ZMod p)) _ _ (fun i => rfl)
  have hτω : τ.comp (ρ k ι hι w (range_subset_of_ker k p L ι hι ε hε w hw1)) = ρ k ι hι w (range_subset_of_ker k p L ι hι ε hε w hw1) :=
    pt_injective k ι hι (by rw [← Gmap_pt, hω, hτ])

  have hbot : ∀ a, nabla k p (AK k p ε) (ρ k ι hι w (range_subset_of_ker k p L ι hι ε hε w hw1) a) ∈ (⊥ : Subalgebra k (AK k p ε)) :=
    fun a => nabla_mem_bot_of_rot_eq k p (AK k p ε) (fun d => by rw [pow_p_eq]; exact Subalgebra.algebraMap_mem _ _) _
      (AlgHom.congr_fun hτω a)
  let χ : A →ₐ[k] k := (εK k p ε).comp (nab.comp (ρ k ι hι w (range_subset_of_ker k p L ι hι ε hε w hw1)))
  have hχ : nab.comp (ρ k ι hι w (range_subset_of_ker k p L ι hι ε hε w hw1)) = (Algebra.ofId k (AK k p ε)).comp χ := by
    apply AlgHom.ext; intro a
    obtain ⟨c, hc'⟩ := Algebra.mem_bot.1 (hbot a)
    change nabla k p (AK k p ε) (ρ k ι hι w _ a) = algebraMap k (AK k p ε) (εK k p ε (nabla k p (AK k p ε) (ρ k ι hι w _ a)))
    rw [← hc', AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]

  have h4 : L.nsmul _ p (uK k p ι hι ε) = Gmap (Algebra.ofId k (AK k p ε)) (pt k ι hι χ (f := f)) := by
    rw [Gmap_pt, ← hχ, ← Gmap_pt, hω]
    let nabH : Pts k f (TP k p (AK k p ε)) →* Pts k f (AK k p ε) := MonoidHom.mk' (Gmap nab) (Gmap_mul L nab)
    change _ = nabH w
    rw [show w = ∏ i : ZMod p, Gmap (ιi i) (uK k p ι hι ε) from rfl, map_prod]
    have h1 : ∀ i, nabH (Gmap (ιi i) (uK k p ι hι ε)) = uK (f := f) k p ι hι ε := by
      intro i
      change Gmap nab (Gmap (ιi i) (uK k p ι hι ε)) = _
      rw [Gmap_comp, show nab.comp (ιi i) = AlgHom.id k (AK k p ε) from AlgHom.ext fun d => nabla_singleAlgHom k p (AK k p ε) i d,
        Gmap_id]
    simp only [h1, Finset.prod_const, Finset.card_univ, ZMod.card]
    exact (pow_eq_nsmul k L _ _).symm

  have h5 : pt k ι hι χ (f := f) = L.one _ := by
    have h6 := congrArg (Gmap (εK k p ε)) h4
    rw [Gmap_nsmul, uK, Gmap_pt, εK_comp_mk, hε, L.nsmul_unit, Gmap_comp,
      algHom_self_eq_id k ((εK k p ε).comp (Algebra.ofId k (AK k p ε))), Gmap_id] at h6
    exact h6.symm
  rw [h4, h5, Gmap_one]

include hc hε in

theorem nsmul_eq_one_of_ker {B : Type u} [CommRing B] [Algebra k B] (z : Pts k f B)
    (hz : frobPt k p f z = L.one _) : L.nsmul _ p z = L.one _ := by
  obtain ⟨ζ', rfl⟩ := exists_eq_Gmap_uK k p L ι hι ε hε z hz
  rw [← Gmap_nsmul, nsmul_uK k p L hc ι hι ε hε, Gmap_one]

include hc hε in

theorem nsmul_eq_of_frob_eq {B : Type u} [CommRing B] [Algebra k B] (x y : Pts k f B)
    (h : frobPt k p f x = frobPt k p f y) : L.nsmul _ p x = L.nsmul _ p y := by
  letI grp : CommGroup (Pts k f B) := { L.pointGroup (sOf k B) with mul_comm := hc _ }
  letI grpF : CommGroup (Pts k f (FrobTwist k p B)) := { L.pointGroup (sOf k (FrobTwist k p B)) with mul_comm := hc _ }
  let Φ : Pts k f B →* Pts k f (FrobTwist k p B) := MonoidHom.mk' (Gmap (frobAlgHom k p B)) (Gmap_mul L _)
  have hz : Φ (x * y⁻¹) = 1 := by
    rw [map_mul, map_inv]
    change frobPt k p f x * (frobPt k p f y)⁻¹ = 1
    rw [h, mul_inv_cancel]
  have h1 := nsmul_eq_one_of_ker k p L hc ι hι ε hε (x * y⁻¹) hz
  rw [← pow_eq_nsmul k L] at h1
  rw [← pow_eq_nsmul k L, ← pow_eq_nsmul k L]
  change x ^ p = y ^ p
  rw [show x = (x * y⁻¹) * y by rw [inv_mul_cancel_right], mul_pow]
  change (x * y⁻¹) ^ p * y ^ p = y ^ p
  rw [h1]
  exact one_mul _

end Universal
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_nsmulPt_eq_of_mapPt_relFrobenius_eq.RelVersch.FrobTwist"

section Main

variable (k : Type u) [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hX : (p : Γ(X, ⊤)) = 0)
  {A : Type u} [CommRing A] [Algebra k A] (ι : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion ι] (hι : ι ≫ f = sOf k A)
  (ε : A →ₐ[k] k) (hε : pt k ι hι ε = L.one (sOf k k))

include hc hε in

theorem affine_case (B : Type u) [CommRing B] (g₁ g₂ : Spec (CommRingCat.of B) ⟶ X) (hg : g₁ ≫ f = g₂ ≫ f)
    (h : g₁ ≫ X.frobenius p 1 hp.out hX = g₂ ≫ X.frobenius p 1 hp.out hX) :
    g₁ ≫ L.schemeNsmul p = g₂ ≫ L.schemeNsmul p := by
  letI : Algebra k B := (Spec.preimage (g₁ ≫ f)).hom.toAlgebra
  have hs : sOf k B = g₁ ≫ f := Spec.map_preimage _
  let x : Pts k f B := ⟨g₁, hs.symm⟩
  let y : Pts k f B := ⟨g₂, hg.symm.trans hs.symm⟩
  have hxy : frobPt k p f x = frobPt k p f y :=
    Subtype.ext (by rw [frobPt_coe k p f hX x, frobPt_coe k p f hX y]; exact h)
  have h1 := congrArg Subtype.val (nsmul_eq_of_frob_eq k p L hc ι hι ε hε x y hxy)
  rw [← comp_schemeNsmul L x p, ← comp_schemeNsmul L y p] at h1
  exact h1

include hc in
theorem comp_schemeNsmul_eq {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ X) (hg : g₁ ≫ f = g₂ ≫ f)
    (h : g₁ ≫ X.frobenius p 1 hp.out hX = g₂ ≫ X.frobenius p 1 hp.out hX) :
    g₁ ≫ L.schemeNsmul p = g₂ ≫ L.schemeNsmul p := by
  classical

  let e₀ : Pts k f k := L.one (sOf k k)
  let q₀ : Spec (CommRingCat.of k) := IsLocalRing.closedPoint k
  let x₀ : X := e₀.1 q₀
  let j := X.affineCover.idx x₀
  let Acat : CommRingCat.{u} := X.affineOpenCover.X j
  let ι' : Spec (CommRingCat.of Acat) ⟶ X := X.affineCover.f j
  haveI : IsOpenImmersion ι' := inferInstanceAs (IsOpenImmersion (X.affineCover.f j))
  letI : Algebra k Acat := (Spec.preimage (ι' ≫ f)).hom.toAlgebra
  have hι' : ι' ≫ f = sOf k Acat := (Spec.map_preimage _).symm
  have he₀ : Set.range e₀.1 ⊆ Set.range ι' := by
    rintro _ ⟨q, rfl⟩
    have hq : q = q₀ := PrimeSpectrum.ext ((Ideal.eq_bot_of_prime _).trans (Ideal.eq_bot_of_prime _).symm)
    rw [hq]
    exact X.affineCover.covers x₀
  let ε' : Acat →ₐ[k] k := ρ k ι' hι' e₀ he₀
  have hε' : pt k ι' hι' ε' = L.one (sOf k k) := pt_ρ k ι' hι' e₀ he₀

  refine Z.affineCover.hom_ext _ _ fun jz => ?_
  rw [← Category.assoc, ← Category.assoc]
  have hg' : (Z.affineCover.f jz ≫ g₁) ≫ f = (Z.affineCover.f jz ≫ g₂) ≫ f := by
    rw [Category.assoc, Category.assoc, hg]
  have h' : (Z.affineCover.f jz ≫ g₁) ≫ X.frobenius p 1 hp.out hX = (Z.affineCover.f jz ≫ g₂) ≫ X.frobenius p 1 hp.out hX := by
    rw [Category.assoc, Category.assoc, h]
  exact affine_case k p L hc hX ι' hι' ε' hε' (Z.affineOpenCover.X jz) _ _ hg' h'

end Main
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_nsmulPt_eq_of_mapPt_relFrobenius_eq.RelVersch.FrobTwist"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_nsmulPt_eq_of_mapPt_relFrobenius_eq.RelVersch.FrobTwist"

end RelVersch
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_nsmulPt_eq_of_mapPt_relFrobenius_eq.RelVersch.FrobTwist P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_nsmulPt_eq_of_mapPt_relFrobenius_eq.RelVersch"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_nsmulPt_eq_of_mapPt_relFrobenius_eq.CerednikDrinfeld CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_nsmulPt_eq_of_mapPt_relFrobenius_eq.CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve"
open scoped Quaternion

namespace CerednikDrinfeld p2m_export "CerednikDrinfeld" "QM.FakeEllipticCurve" namespace QM p2m_export "CerednikDrinfeld.QM" "mapPt FactorsThrough nsmulPt FakeEllipticCurve" end CerednikDrinfeld.QM
p2m_open_scoped "CerednikDrinfeld CerednikDrinfeld.QM" in

theorem CerednikDrinfeld.QM.nsmulPt_eq_nsmul {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : GoodReductionJacobian.RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    nsmulPt L t n P = L.nsmul t n P := by
  induction n with
  | zero => rfl
  | succ n ih => rw [GoodReductionJacobian.RelativeGroupLaw.nsmul_succ, ← ih]; rfl

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k : Type u) [Field k] (ℓ : ℕ) [hℓ : Fact ℓ.Prime] [CharP k ℓ]
    (E Eℓ : FakeEllipticCurve Λ N k)
    (pr : Eℓ.A ⟶ E.A)
    (pr_isPullback : CategoryTheory.IsPullback pr Eℓ.f E.f (Spec.map (CommRingCat.ofHom (frobenius k ℓ))))
    (pr_mul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t' Eℓ.f),
      (Eℓ.L.mul t' P Q).1 ≫ pr =
        (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (frobenius k ℓ)))
          ⟨P.1 ≫ pr, by rw [Category.assoc, pr_isPullback.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ pr, by rw [Category.assoc, pr_isPullback.w, ← Category.assoc, Q.2]⟩).1)
    (pr_act : ∀ x : ↥Λ, Eℓ.act x ≫ pr = pr ≫ E.act x)
    (pr_lev : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t' Eℓ.f),
      FactorsThrough Eℓ.lev P → ∃ P₀ : T ⟶ E.C, P₀ ≫ E.lev = P.1 ≫ pr)
    (pr_lev' : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t' Eℓ.f),
      (∃ P₀ : T ⟶ E.C, P₀ ≫ E.lev = P.1 ≫ pr) → FactorsThrough Eℓ.lev P)
    (hA : (ℓ : Γ(E.A, ⊤)) = 0)
    (F : E.A ⟶ Eℓ.A) (F_over : F ≫ Eℓ.f = E.f) (F_pr : F ≫ pr = E.A.frobenius ℓ 1 hℓ.out hA)
    (F_hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
      mapPt F F_over (E.L.mul t P Q) = Eℓ.L.mul t (mapPt F F_over P) (mapPt F F_over Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (g₁ g₂ : SchemeHomOver t E.f)
    (h : mapPt F F_over g₁ = mapPt F F_over g₂) :
    nsmulPt E.L t ℓ g₁ = nsmulPt E.L t ℓ g₂ := by
  have h1 : g₁.1 ≫ F = g₂.1 ≫ F := congrArg Subtype.val h
  have h2 : g₁.1 ≫ E.A.frobenius ℓ 1 hℓ.out hA = g₂.1 ≫ E.A.frobenius ℓ 1 hℓ.out hA := by
    rw [← F_pr, ← Category.assoc, h1, Category.assoc]
  have hg : g₁.1 ≫ E.f = g₂.1 ≫ E.f := by rw [g₁.2, g₂.2]
  have h3 := RelVersch.comp_schemeNsmul_eq k ℓ E.L E.comm hA g₁.1 g₂.1 hg h2
  rw [RelVersch.comp_schemeNsmul E.L g₁ ℓ, RelVersch.comp_schemeNsmul E.L g₂ ℓ] at h3
  rw [nsmulPt_eq_nsmul, nsmulPt_eq_nsmul]
  exact Subtype.ext h3

end S_CerednikDrinfeld_QM_FakeEllipticCurve_nsmulPt_eq_of_mapPt_relFrobenius_eq
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_nsmulPt_eq_of_mapPt_relFrobenius_eq (solution)
