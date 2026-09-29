-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_forall_factorsThrough_iff_exists_sectionAt_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/67950679-2ede-53fc-94f8-ad30a3c610e9

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_iff_exists_sectionAt_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

noncomputable section

namespace ConstExtraLevelBaseSol

section Geometric

variable {S : Type} [CommRing S]

abbrev BS (S : Type) [CommRing S] : Scheme.{0} := Spec (CommRingCat.of S)

def ringHomOf {k : Type} [Field k] (b : Spec (CommRingCat.of k) ⟶ BS S) : S →+* k :=
  (Spec.preimage b).hom

theorem geomPoint_ringHomOf {k : Type} [Field k] (b : Spec (CommRingCat.of k) ⟶ BS S) :
    geomPoint k (ringHomOf b) = b := by
  unfold geomPoint ringHomOf
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]

theorem exists_eq_comp_of_mem_range {k : Type} [Field k] {Z X : Scheme.{0}} (σ : Z ⟶ X) [IsClosedImmersion σ]
    (x : Spec (CommRingCat.of k) ⟶ X) (p : Spec (CommRingCat.of k)) (hx : x.base p ∈ Set.range σ.base) :
    ∃ b : Spec (CommRingCat.of k) ⟶ Z, x = b ≫ σ := by
  obtain ⟨z, hz⟩ := hx
  haveI : IsClosedImmersion (pullback.fst x σ) := MorphismProperty.pullback_fst _ _ inferInstance
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := x) (g := σ) p z hz.symm
  haveI : Surjective (pullback.fst x σ) := ⟨fun s => ⟨w, by rw [hw]; exact Subsingleton.elim _ _⟩⟩
  haveI : IsIso (pullback.fst x σ) := isIso_of_isClosedImmersion_of_surjective _
  refine ⟨inv (pullback.fst x σ) ≫ pullback.snd x σ, ?_⟩
  rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]

def geomPtAt (X : Scheme.{0}) (x : X) : Spec (CommRingCat.of (AlgebraicClosure (X.residueField x))) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) (AlgebraicClosure (X.residueField x)))) ≫
    X.fromSpecResidueField x

theorem geomPtAt_apply (X : Scheme.{0}) (x : X) (p : Spec (CommRingCat.of (AlgebraicClosure (X.residueField x)))) :
    (geomPtAt X x).base p = x := by
  simp only [geomPtAt, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]
  exact Scheme.fromSpecResidueField_apply x _

end Geometric

section Setup

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
variable {S : Type} [CommRing S] {E : FakeEllipticCurve Λ N S} {ι : Type}

abbrev Sec (E : FakeEllipticCurve Λ N S) : Type := SchemeHomOver (𝟙 (BS S)) E.f

variable (W : ι → Sec E)

abbrev fam (S : Type) [CommRing S] (ι : Type) : ι → Scheme.{0} := fun _ => BS S

abbrev KW (S : Type) [CommRing S] (ι : Type) : Scheme.{0} := ∐ fam S ι

scoped instance isOpenImmersion_sigmaι (S : Type) [CommRing S] (ι : Type) (i : ι) : IsOpenImmersion (Sigma.ι (fam S ι) i) :=
  Scheme.IsLocallyDirected.instIsOpenImmersionι (Discrete.functor (fam S ι)) ⟨i⟩

private def _root_.ConstExtraLevelBaseSol.levK : KW S ι ⟶ E.A := Sigma.desc fun i : ι => (W i).1

p2m_export "ConstExtraLevelBaseSol" "levK"

def πK (S : Type) [CommRing S] (ι : Type) : KW S ι ⟶ BS S := Sigma.desc fun _ : ι => 𝟙 (BS S)

@[scoped simp, reassoc] theorem ιK_levK (i : ι) : Sigma.ι (fam S ι) i ≫ levK W = (W i).1 :=
  Sigma.ι_desc _ _

@[scoped simp, reassoc] theorem ιK_πK (i : ι) : Sigma.ι (fam S ι) i ≫ πK S ι = 𝟙 _ :=
  Sigma.ι_desc _ _

@[scoped simp, reassoc] theorem levK_f : levK W ≫ E.f = πK S ι := by
  refine Sigma.hom_ext _ _ fun i => ?_
  rw [ιK_levK_assoc, ιK_πK]
  exact (W i).2

theorem exists_ιK_eq (x : KW S ι) : ∃ (i : ι) (s : BS S), Sigma.ι (fam S ι) i s = x := by
  obtain ⟨⟨i, s⟩, rfl⟩ := (sigmaMk (fam S ι)).surjective x
  exact ⟨i, s, by rw [← sigmaMk_mk]⟩

theorem isClosedImmersion_sec (w : Sec E) : IsClosedImmersion w.1 := by
  haveI : IsSeparated E.f := by
    haveI := E.bundle.proper
    infer_instance
  haveI : IsClosedImmersion (w.1 ≫ E.f) := by rw [w.2]; infer_instance
  exact IsClosedImmersion.of_comp w.1 E.f

theorem sec_base_f (w : Sec E) (s : BS S) : E.f.base (w.1.base s) = s := by
  rw [← Scheme.Hom.comp_apply, w.2]; rfl

theorem levK_apply_ιK (i : ι) (s : BS S) : (levK W).base (Sigma.ι (fam S ι) i s) = (W i).1.base s := by
  rw [← Scheme.Hom.comp_apply, ιK_levK]

variable (hW_inj : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (i j : ι),
  FakeEllipticCurve.sectionAt (W i) k sk = FakeEllipticCurve.sectionAt (W j) k sk → i = j)

include hW_inj in

theorem eq_of_base_eq (i j : ι) (s : BS S) (h : (W i).1.base s = (W j).1.base s) : i = j := by
  set x := (W i).1.base s with hx
  let k := AlgebraicClosure (E.A.residueField x)
  haveI := isClosedImmersion_sec (W i)
  haveI := isClosedImmersion_sec (W j)
  let p : Spec (CommRingCat.of k) := IsLocalRing.closedPoint k
  obtain ⟨c, hc⟩ := exists_eq_comp_of_mem_range (W i).1 (geomPtAt E.A x) p
    (by rw [geomPtAt_apply]; exact ⟨s, rfl⟩)
  obtain ⟨c', hc'⟩ := exists_eq_comp_of_mem_range (W j).1 (geomPtAt E.A x) p
    (by rw [geomPtAt_apply]; exact ⟨s, h.symm⟩)
  have hcc' : c = c' := by
    calc c = c ≫ (W i).1 ≫ E.f := by rw [(W i).2, Category.comp_id]
      _ = geomPtAt E.A x ≫ E.f := by rw [← Category.assoc, ← hc]
      _ = c' ≫ (W j).1 ≫ E.f := by rw [hc', Category.assoc]
      _ = c' := by rw [(W j).2, Category.comp_id]
  refine hW_inj k (ringHomOf c) i j (Subtype.ext ?_)
  show geomPoint k (ringHomOf c) ≫ (W i).1 = geomPoint k (ringHomOf c) ≫ (W j).1
  rw [geomPoint_ringHomOf, ← hc, hcc', ← hc']

include hW_inj in

theorem injective_levK_base : Function.Injective (levK W).base := by
  intro x y h
  obtain ⟨i, s, rfl⟩ := exists_ιK_eq x
  obtain ⟨j, s', rfl⟩ := exists_ιK_eq y
  rw [levK_apply_ιK, levK_apply_ιK] at h
  have hs : s = s' := by rw [← sec_base_f (W i) s, h, sec_base_f]
  subst hs
  obtain rfl := eq_of_base_eq W hW_inj i j s h
  rfl

theorem isClosed_image_levK [Finite ι] (Z : Set (KW S ι)) (hZ : IsClosed Z) : IsClosed ((levK W).base '' Z) := by
  have hdec : (levK W).base '' Z = ⋃ i : ι, (W i).1.base '' ((Sigma.ι (fam S ι) i).base ⁻¹' Z) := by
    ext y
    simp only [Set.mem_image, Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨i, s, rfl⟩ := exists_ιK_eq x
      exact ⟨i, s, hx, (levK_apply_ιK W i s).symm⟩
    · rintro ⟨i, s, hs, rfl⟩
      exact ⟨_, hs, levK_apply_ιK W i s⟩
  rw [hdec]
  refine isClosed_iUnion_of_finite fun i => ?_
  haveI := isClosedImmersion_sec (W i)
  exact (W i).1.isClosedEmbedding.isClosedMap _ (hZ.preimage (Sigma.ι (fam S ι) i).continuous)

include hW_inj in

theorem isClosedImmersion_levK [Finite ι] : IsClosedImmersion (levK W) := by

  haveI : SurjectiveOnStalks (levK W) := by
    refine IsZariskiLocalAtSource.of_openCover (P := @SurjectiveOnStalks) (sigmaOpenCover (fam S ι)) fun i' => ?_
    obtain ⟨i, hi⟩ : ∃ i : ι, i = i' := ⟨i', rfl⟩
    subst hi
    haveI := isClosedImmersion_sec (W i)
    have h : (sigmaOpenCover (fam S ι)).f i ≫ levK W = (W i).1 := by
      rw [sigmaOpenCover_f]; exact Sigma.ι_desc _ _
    rw [h]
    exact (isClosedImmersion_sec (W i)).toSurjectiveOnStalks
  rw [isClosedImmersion_iff]
  refine ⟨inferInstance, ?_⟩
  exact Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap (levK W).continuous
    (injective_levK_base W hW_inj) fun Z hZ => isClosed_image_levK W Z hZ

end Setup

section Naturality

variable {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)

theorem inv_natural {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (G.inv t x) = G.inv t' (schemeHomOverComp ψ hψ x) := by
  letI := G.pointGroup t'
  have h : G.mul t' (schemeHomOverComp ψ hψ (G.inv t x)) (schemeHomOverComp ψ hψ x) = G.one t' := by
    rw [← G.mul_natural, G.inv_mul_cancel, G.one_natural]
  have h' : (schemeHomOverComp ψ hψ (G.inv t x)) * (schemeHomOverComp ψ hψ x) = 1 := h
  exact eq_inv_of_mul_eq_one_left h'

theorem nsmul_natural {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (n : ℕ) (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (nsmulPt G t n x) = nsmulPt G t' n (schemeHomOverComp ψ hψ x) := by
  induction n with
  | zero => exact G.one_natural t t' ψ hψ
  | succ n ih =>
    show schemeHomOverComp ψ hψ (G.mul t (nsmulPt G t n x) x) = G.mul t' (nsmulPt G t' n _) _
    rw [G.mul_natural, ih]

theorem eq_one_of_mul_self {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f)
    (h : G.mul t x x = x) : x = G.one t := by
  letI := G.pointGroup t
  have h' : x * x = x := h
  exact mul_left_cancel (h'.trans (mul_one x).symm)

theorem inv_eq_of_mul_eq_one {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f)
    (h : G.mul t x y = G.one t) : G.inv t y = x := by
  letI := G.pointGroup t
  have h' : x * y = 1 := h
  exact (eq_inv_of_mul_eq_one_left h').symm

end Naturality

section Family

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
variable {S : Type} [CommRing S] {E : FakeEllipticCurve Λ N S} {ℓ : ℕ}
variable {W : ZMod ℓ × ZMod ℓ → Sec E}
variable (hW_add : ∀ i j : ZMod ℓ × ZMod ℓ, W (i + j) = E.L.mul (𝟙 (BS S)) (W i) (W j))

include hW_add

theorem W_zero : W 0 = E.L.one (𝟙 (BS S)) :=
  eq_one_of_mul_self E.L _ _ (by rw [← hW_add, add_zero])

theorem W_neg (i : ZMod ℓ × ZMod ℓ) : E.L.inv (𝟙 (BS S)) (W i) = W (-i) :=
  inv_eq_of_mul_eq_one E.L _ _ _ (by rw [← hW_add, neg_add_cancel, W_zero hW_add])

theorem W_nsmul (n : ℕ) (i : ZMod ℓ × ZMod ℓ) : nsmulPt E.L (𝟙 (BS S)) n (W i) = W (n • i) := by
  induction n with
  | zero => rw [zero_smul]; exact (W_zero hW_add).symm
  | succ n ih =>
    show E.L.mul _ (nsmulPt E.L _ n (W i)) (W i) = W ((n + 1) • i)
    rw [ih, succ_nsmul, hW_add]

theorem W_torsion (i : ZMod ℓ × ZMod ℓ) : nsmulPt E.L (𝟙 (BS S)) ℓ (W i) = E.L.one (𝟙 (BS S)) := by
  rw [W_nsmul hW_add, ← W_zero hW_add]
  congr 1
  ext <;> simp

end Family

section Points

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
variable {S : Type} [CommRing S] {E : FakeEllipticCurve Λ N S} {ι : Type} (W : ι → Sec E)

def piece {T : Scheme.{0}} (P₀ : T ⟶ KW S ι) (i : ι) : T.Opens := P₀ ⁻¹ᵁ (Sigma.ι (fam S ι) i).opensRange

theorem mem_piece_iff {T : Scheme.{0}} (P₀ : T ⟶ KW S ι) (i : ι) (τ : T) :
    τ ∈ piece P₀ i ↔ P₀.base τ ∈ Set.range (Sigma.ι (fam S ι) i).base := by rfl

theorem isOpenCover_piece {T : Scheme.{0}} (P₀ : T ⟶ KW S ι) : TopologicalSpace.IsOpenCover (piece P₀) := by
  apply TopologicalSpace.IsOpenCover.mk
  rw [eq_top_iff]
  intro τ _
  rw [TopologicalSpace.Opens.mem_iSup]
  obtain ⟨i, s, hs⟩ := exists_ιK_eq (P₀.base τ)
  exact ⟨i, (mem_piece_iff P₀ i τ).mpr ⟨_, hs⟩⟩

def cover {T : Scheme.{0}} (P₀ : T ⟶ KW S ι) : T.OpenCover :=
  T.openCoverOfIsOpenCover (piece P₀) (isOpenCover_piece P₀)

@[scoped simp] theorem cover_f {T : Scheme.{0}} (P₀ : T ⟶ KW S ι) (i : ι) : (cover P₀).f i = (piece P₀ i).ι := by
  simp [cover]

theorem disjoint_piece {T : Scheme.{0}} (P₀ : T ⟶ KW S ι) {i j : ι} (h : i ≠ j) :
    Disjoint (piece P₀ i) (piece P₀ j) := by
  have hd := disjoint_opensRange_sigmaι (fam S ι) i j h
  rw [disjoint_iff] at hd ⊢
  show P₀ ⁻¹ᵁ _ ⊓ P₀ ⁻¹ᵁ _ = ⊥
  rw [← Scheme.Hom.preimage_inf, hd, Scheme.Hom.preimage_bot]

theorem restrict_levK_eq {T : Scheme.{0}} (P₀ : T ⟶ KW S ι) (i : ι) (U : T.Opens) (hU : U ≤ piece P₀ i) :
    U.ι ≫ P₀ ≫ levK W = (U.ι ≫ P₀ ≫ πK S ι) ≫ (W i).1 := by
  have hrange : Set.range (U.ι ≫ P₀).base ⊆ Set.range (Sigma.ι (fam S ι) i).base := by
    rintro _ ⟨τ, rfl⟩
    have hτ := (mem_piece_iff P₀ i τ.1).mp (hU τ.2)
    simpa [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] using hτ
  let g := IsOpenImmersion.lift (Sigma.ι (fam S ι) i) (U.ι ≫ P₀) hrange
  have hfac : g ≫ Sigma.ι (fam S ι) i = U.ι ≫ P₀ := IsOpenImmersion.lift_fac _ _ hrange
  calc U.ι ≫ P₀ ≫ levK W = (U.ι ≫ P₀) ≫ levK W := (Category.assoc _ _ _).symm
    _ = (g ≫ Sigma.ι (fam S ι) i) ≫ levK W := by rw [hfac]
    _ = g ≫ (W i).1 := by rw [Category.assoc, ιK_levK]
    _ = (g ≫ Sigma.ι (fam S ι) i ≫ πK S ι) ≫ (W i).1 := by rw [ιK_πK, Category.comp_id]
    _ = (U.ι ≫ P₀ ≫ πK S ι) ≫ (W i).1 := by rw [← Category.assoc g, hfac]; simp only [Category.assoc]

variable {W}

theorem base_eq {T : Scheme.{0}} {t : T ⟶ BS S} (P : SchemeHomOver t E.f) (P₀ : T ⟶ KW S ι)
    (hP : P₀ ≫ levK W = P.1) : P₀ ≫ πK S ι = t := by
  rw [← levK_f, ← Category.assoc, hP]; exact P.2

def constPt {T : Scheme.{0}} (t : T ⟶ BS S) (w : Sec E) : SchemeHomOver t E.f :=
  schemeHomOverComp t (Category.comp_id t) w

@[scoped simp] theorem constPt_coe {T : Scheme.{0}} (t : T ⟶ BS S) (w : Sec E) : (constPt t w).1 = t ≫ w.1 := rfl

theorem sectionAt_eq_constPt (w : Sec E) (k : Type) [Field k] (sk : S →+* k) :
    FakeEllipticCurve.sectionAt w k sk = constPt (geomPoint k sk) w := rfl

theorem constPt_id (w : Sec E) : constPt (𝟙 (BS S)) w = w := Subtype.ext (Category.id_comp _)

theorem constPt_comp {T T' : Scheme.{0}} (t : T ⟶ BS S) (t' : T' ⟶ BS S) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (w : Sec E) :
    schemeHomOverComp ψ hψ (constPt t w) = constPt t' w := by
  apply Subtype.ext
  simp [constPt, schemeHomOverComp, ← hψ]

theorem constPt_mul {T : Scheme.{0}} (t : T ⟶ BS S) (v w : Sec E) :
    E.L.mul t (constPt t v) (constPt t w) = constPt t (E.L.mul _ v w) := by
  unfold constPt; rw [← E.L.mul_natural]

theorem constPt_one {T : Scheme.{0}} (t : T ⟶ BS S) : constPt t (E.L.one _) = E.L.one t := by
  unfold constPt; rw [E.L.one_natural]

theorem constPt_inv {T : Scheme.{0}} (t : T ⟶ BS S) (w : Sec E) : E.L.inv t (constPt t w) = constPt t (E.L.inv _ w) := by
  unfold constPt; rw [← inv_natural]

theorem constPt_nsmul {T : Scheme.{0}} (t : T ⟶ BS S) (n : ℕ) (w : Sec E) :
    nsmulPt E.L t n (constPt t w) = constPt t (nsmulPt E.L _ n w) := by
  unfold constPt; rw [← nsmul_natural]

theorem constPt_act {T : Scheme.{0}} (t : T ⟶ BS S) (x : ↥Λ) (w : Sec E) :
    pushPt (E.act x) (E.act_over x) (constPt t w) = constPt t (pushPt (E.act x) (E.act_over x) w) := by
  apply Subtype.ext
  simp [constPt, schemeHomOverComp, pushPt, mapPt]

theorem restrict_eq_constPt {T : Scheme.{0}} {t : T ⟶ BS S} (P : SchemeHomOver t E.f) (P₀ : T ⟶ KW S ι)
    (hP : P₀ ≫ levK W = P.1) (i : ι) (U : T.Opens) (hU : U ≤ piece P₀ i) :
    schemeHomOverComp U.ι rfl P = constPt (U.ι ≫ t) (W i) := by
  apply Subtype.ext
  show U.ι ≫ P.1 = (U.ι ≫ t) ≫ (W i).1
  rw [← hP, restrict_levK_eq W P₀ i U hU, base_eq P P₀ hP]

theorem factorsThrough_constPt {T : Scheme.{0}} (t : T ⟶ BS S) (i : ι) :
    FactorsThrough (levK W) (constPt t (W i)) :=
  ⟨t ≫ Sigma.ι (fam S ι) i, by rw [Category.assoc, ιK_levK]; rfl⟩

theorem eq_of_forall_piece {T : Scheme.{0}} {t : T ⟶ BS S} (P₀ : T ⟶ KW S ι) (P Q : SchemeHomOver t E.f)
    (h : ∀ i : ι, schemeHomOverComp (piece P₀ i).ι rfl P = schemeHomOverComp (piece P₀ i).ι rfl Q) : P = Q := by
  apply Subtype.ext
  refine Scheme.Cover.hom_ext (cover P₀) _ _ fun i' => ?_
  obtain ⟨i, hi⟩ : ∃ i : ι, i = i' := ⟨i', rfl⟩
  subst hi
  rw [cover_f]
  exact congrArg Subtype.val (h i)

def permK (σ : ι → ι) : KW S ι ⟶ KW S ι := Sigma.desc fun i : ι => Sigma.ι (fam S ι) (σ i)

@[scoped simp, reassoc] theorem ι_permK (σ : ι → ι) (i : ι) : Sigma.ι (fam S ι) i ≫ permK σ = Sigma.ι (fam S ι) (σ i) :=
  Sigma.ι_desc _ _

@[scoped simp, reassoc] theorem permK_πK (σ : ι → ι) : permK σ ≫ πK S ι = πK S ι :=
  Sigma.hom_ext _ _ fun i => by rw [ι_permK_assoc, ιK_πK, ιK_πK]

theorem piece_le_piece_permK {T : Scheme.{0}} (P₀ : T ⟶ KW S ι) (σ : ι → ι) (i : ι) :
    piece P₀ i ≤ piece (P₀ ≫ permK σ) (σ i) := by
  intro τ hτ
  obtain ⟨y, hy⟩ := (mem_piece_iff P₀ i τ).mp hτ
  refine (mem_piece_iff _ _ τ).mpr ⟨y, ?_⟩
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply, ← hy, ← Scheme.Hom.comp_apply, ι_permK]

def ptOf (W : ι → Sec E) {T : Scheme.{0}} (t : T ⟶ BS S) (Q₀ : T ⟶ KW S ι) (hQ : Q₀ ≫ πK S ι = t) : SchemeHomOver t E.f :=
  ⟨Q₀ ≫ levK W, by rw [Category.assoc, levK_f, hQ]⟩

@[scoped simp] theorem ptOf_coe (W : ι → Sec E) {T : Scheme.{0}} (t : T ⟶ BS S) (Q₀ : T ⟶ KW S ι) (hQ : Q₀ ≫ πK S ι = t) :
    (ptOf W t Q₀ hQ).1 = Q₀ ≫ levK W := rfl

theorem factorsThrough_ptOf (W : ι → Sec E) {T : Scheme.{0}} (t : T ⟶ BS S) (Q₀ : T ⟶ KW S ι) (hQ : Q₀ ≫ πK S ι = t) :
    FactorsThrough (levK W) (ptOf W t Q₀ hQ) := ⟨Q₀, rfl⟩

theorem factorsThrough_of_unary {T : Scheme.{0}} (t : T ⟶ BS S)
    (op : ∀ {T' : Scheme.{0}} (t' : T' ⟶ BS S), SchemeHomOver t' E.f → SchemeHomOver t' E.f)
    (hop : ∀ {T' : Scheme.{0}} (t' : T' ⟶ BS S) (U : T'.Opens) (P : SchemeHomOver t' E.f),
      schemeHomOverComp U.ι rfl (op t' P) = op (U.ι ≫ t') (schemeHomOverComp U.ι rfl P))
    (hconst : ∀ {T' : Scheme.{0}} (t' : T' ⟶ BS S) (w : Sec E), op t' (constPt t' w) = constPt t' (op (𝟙 _) w))
    (σ : ι → ι) (hσ : ∀ i, op (𝟙 _) (W i) = W (σ i))
    (P : SchemeHomOver t E.f) (hP : FactorsThrough (levK W) P) : FactorsThrough (levK W) (op t P) := by
  obtain ⟨P₀, hP₀⟩ := hP
  have hQ : (P₀ ≫ permK σ) ≫ πK S ι = t := by rw [Category.assoc, permK_πK, base_eq P P₀ hP₀]
  suffices h : op t P = ptOf W t (P₀ ≫ permK σ) hQ by rw [h]; exact factorsThrough_ptOf W _ _ _
  refine eq_of_forall_piece P₀ _ _ fun i => ?_
  rw [hop, restrict_eq_constPt P P₀ hP₀ i _ le_rfl, hconst, hσ,
    restrict_eq_constPt (ptOf W t (P₀ ≫ permK σ) hQ) (P₀ ≫ permK σ) rfl (σ i) _ (piece_le_piece_permK P₀ σ i)]

theorem levK_nsmul {n : ℕ} (hn : ∀ i, nsmulPt E.L (𝟙 (BS S)) n (W i) = E.L.one _)
    {T : Scheme.{0}} (t : T ⟶ BS S) (P : SchemeHomOver t E.f) (hP : FactorsThrough (levK W) P) :
    nsmulPt E.L t n P = E.L.one t := by
  obtain ⟨P₀, hP₀⟩ := hP
  refine eq_of_forall_piece P₀ _ _ fun i => ?_
  rw [nsmul_natural, restrict_eq_constPt P P₀ hP₀ i _ le_rfl, constPt_nsmul, hn i, constPt_one, E.L.one_natural]

variable (hW_lev : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (i : ι),
  FactorsThrough E.lev (FakeEllipticCurve.sectionAt (W i) k sk) → W i = E.L.one _)

include hW_lev in

theorem levK_disjoint {T : Scheme.{0}} (t : T ⟶ BS S) (P : SchemeHomOver t E.f)
    (hP : FactorsThrough (levK W) P) (hC : FactorsThrough E.lev P) : P = E.L.one t := by
  obtain ⟨P₀, hP₀⟩ := hP
  obtain ⟨c, hc⟩ := hC
  refine eq_of_forall_piece P₀ _ _ fun i => ?_
  rw [restrict_eq_constPt P P₀ hP₀ i _ le_rfl, E.L.one_natural]
  rcases isEmpty_or_nonempty (piece P₀ i : Scheme.{0}) with hne | hne
  ·
    apply Subtype.ext
    exact IsInitial.hom_ext (X := (piece P₀ i : Scheme.{0})) (isInitialOfIsEmpty) _ _
  ·
    obtain ⟨τ⟩ := hne
    set U := piece P₀ i with hUdef
    let g := geomPtAt (U : Scheme.{0}) τ
    let bpt : Spec (CommRingCat.of (AlgebraicClosure ((U : Scheme.{0}).residueField τ))) ⟶ BS S := g ≫ U.ι ≫ t
    have h1 : U.ι ≫ P.1 = (U.ι ≫ t) ≫ (W i).1 := congrArg Subtype.val (restrict_eq_constPt P P₀ hP₀ i _ le_rfl)
    have hWi : W i = E.L.one _ := by
      refine hW_lev _ (ringHomOf bpt) i ⟨g ≫ U.ι ≫ c, ?_⟩
      show (g ≫ U.ι ≫ c) ≫ E.lev = geomPoint _ (ringHomOf bpt) ≫ (W i).1
      rw [geomPoint_ringHomOf, Category.assoc, Category.assoc, hc, h1]
      simp only [Category.assoc, bpt]
    rw [hWi, constPt_one]

theorem levK_mul (μ : ι → ι → ι) (hμ : ∀ i j, E.L.mul (𝟙 (BS S)) (W i) (W j) = W (μ i j))
    {T : Scheme.{0}} (t : T ⟶ BS S) (P Q : SchemeHomOver t E.f)
    (hP : FactorsThrough (levK W) P) (hQ : FactorsThrough (levK W) Q) :
    FactorsThrough (levK W) (E.L.mul t P Q) := by
  obtain ⟨P₀, hP₀⟩ := hP
  obtain ⟨Q₀, hQ₀⟩ := hQ

  let U : ι × ι → T.Opens := fun p => piece P₀ p.1 ⊓ piece Q₀ p.2
  have hcov : ⨆ p, ((U p).ι).opensRange = ⊤ := by
    simp only [Scheme.Opens.opensRange_ι]
    rw [eq_top_iff]
    intro τ _
    rw [TopologicalSpace.Opens.mem_iSup]
    obtain ⟨v, s, hv⟩ := exists_ιK_eq (P₀.base τ)
    obtain ⟨w, s', hw⟩ := exists_ιK_eq (Q₀.base τ)
    exact ⟨(v, w), (mem_piece_iff P₀ v τ).mpr ⟨_, hv⟩, (mem_piece_iff Q₀ w τ).mpr ⟨_, hw⟩⟩
  have hdisj : Pairwise (Function.onFun Disjoint fun p => ((U p).ι).opensRange) := by
    intro p q hpq
    simp only [Function.onFun, Scheme.Opens.opensRange_ι]
    by_cases h1 : p.1 = q.1
    · have h2 : p.2 ≠ q.2 := fun h2 => hpq (Prod.ext h1 h2)
      exact (disjoint_piece Q₀ h2).mono inf_le_right inf_le_right
    · exact (disjoint_piece P₀ h1).mono inf_le_left inf_le_left
  obtain ⟨hc⟩ := nonempty_isColimit_cofanMk_of (fun p => (U p).ι) hcov hdisj

  let R₀ : T ⟶ KW S ι := Cofan.IsColimit.desc hc fun p => ((U p).ι ≫ t) ≫ Sigma.ι (fam S ι) (μ p.1 p.2)
  have hR₀ : ∀ p, (U p).ι ≫ R₀ = ((U p).ι ≫ t) ≫ Sigma.ι (fam S ι) (μ p.1 p.2) :=
    fun p => Cofan.IsColimit.fac hc _ p
  refine ⟨R₀, Cofan.IsColimit.hom_ext hc _ _ fun p => ?_⟩
  show (U p).ι ≫ R₀ ≫ levK W = (U p).ι ≫ (E.L.mul t P Q).1
  rw [← Category.assoc, hR₀, Category.assoc, ιK_levK]
  have hPU : schemeHomOverComp (U p).ι rfl P = constPt ((U p).ι ≫ t) (W p.1) :=
    restrict_eq_constPt P P₀ hP₀ p.1 (U p) inf_le_left
  have hQU : schemeHomOverComp (U p).ι rfl Q = constPt ((U p).ι ≫ t) (W p.2) :=
    restrict_eq_constPt Q Q₀ hQ₀ p.2 (U p) inf_le_right
  have hnat := E.L.mul_natural t ((U p).ι ≫ t) (U p).ι rfl P Q
  rw [hPU, hQU, constPt_mul, hμ] at hnat
  exact (congrArg Subtype.val hnat).symm

theorem exists_eq_constPt_of_subsingleton {T : Scheme.{0}} [Subsingleton T] [Nonempty T] {t : T ⟶ BS S}
    (P : SchemeHomOver t E.f) (hP : FactorsThrough (levK W) P) : ∃ i : ι, P = constPt t (W i) := by
  obtain ⟨P₀, hP₀⟩ := hP
  obtain ⟨τ₀⟩ := (inferInstance : Nonempty T)
  obtain ⟨i, s, hi⟩ := exists_ιK_eq (P₀.base τ₀)
  refine ⟨i, ?_⟩
  have htop : (⊤ : T.Opens) ≤ piece P₀ i := by
    intro τ _
    rw [Subsingleton.elim τ τ₀]
    exact (mem_piece_iff P₀ i τ₀).mpr ⟨_, hi⟩
  have h := congrArg Subtype.val (restrict_eq_constPt P P₀ hP₀ i ⊤ htop)
  change (⊤ : T.Opens).ι ≫ P.1 = ((⊤ : T.Opens).ι ≫ t) ≫ (W i).1 at h
  haveI : IsIso (⊤ : T.Opens).ι := (inferInstance : IsIso T.topIso.hom)
  rw [Category.assoc, cancel_epi] at h
  exact Subtype.ext h

end Points

section Finiteness

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
variable {S : Type} [CommRing S] {ι : Type}

theorem sigmaOpenCover_f_πK (i' : (sigmaOpenCover (fam S ι)).I₀) : (sigmaOpenCover (fam S ι)).f i' ≫ πK S ι = 𝟙 _ := by
  obtain ⟨i, hi⟩ : ∃ i : ι, i = i' := ⟨i', rfl⟩
  subst hi
  rw [sigmaOpenCover_f]
  exact Sigma.ι_desc _ _

theorem flat_πK : Flat (πK S ι) :=
  IsZariskiLocalAtSource.of_openCover (P := @Flat) (sigmaOpenCover (fam S ι)) fun i => by
    rw [sigmaOpenCover_f_πK]
    exact (inferInstance : Flat (𝟙 (BS S)))

theorem locallyOfFinitePresentation_πK : LocallyOfFinitePresentation (πK S ι) :=
  IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFinitePresentation) (sigmaOpenCover (fam S ι)) fun i => by
    rw [sigmaOpenCover_f_πK]
    exact (inferInstance : LocallyOfFinitePresentation (𝟙 (BS S)))

def diagK (S : Type) [CommRing S] (ι : Type) : CommRingCat.of S ⟶ CommRingCat.of (ι → S) :=
  CommRingCat.ofHom (algebraMap S (ι → S))

theorem πK_eq : πK S ι = sigmaSpec (fun _ : ι => CommRingCat.of S) ≫ Spec.map (diagK S ι) := by
  refine Sigma.hom_ext _ _ fun i => ?_
  rw [ιK_πK, ← Category.assoc]
  erw [ι_sigmaSpec (fun _ : ι => CommRingCat.of S) i]
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1

variable [Fintype ι]

scoped instance moduleFinite_pi (S : Type) [CommRing S] (ι : Type) [Fintype ι] : Module.Finite S (ι → S) := Module.Finite.pi
scoped instance moduleFree_pi (S : Type) [CommRing S] (ι : Type) [Fintype ι] : Module.Free S (ι → S) := Module.Free.pi _ _

scoped instance isFinite_diagK : IsFinite (Spec.map (diagK S ι)) := by
  rw [IsFinite.SpecMap_iff]
  show (algebraMap S (ι → S)).Finite
  rw [RingHom.finite_algebraMap]
  infer_instance

scoped instance flat_diagK : Flat (Spec.map (diagK S ι)) := by
  rw [Flat.SpecMap_iff]
  show (algebraMap S (ι → S)).Flat
  rw [RingHom.flat_algebraMap_iff]
  infer_instance

theorem isFinite_πK : IsFinite (πK S ι) := by
  rw [πK_eq]; infer_instance

theorem finrank_πK (s : BS S) : (πK S ι).finrank s = Nat.card ι := by
  rcases subsingleton_or_nontrivial S with hS | hS
  · exact ((inferInstance : IsEmpty (PrimeSpectrum S)).false s).elim
  rw [πK_eq]
  haveI : IsIso (sigmaSpec fun _ : ι => CommRingCat.of S) := inferInstance
  rw [Scheme.Hom.finrank_comp_left_of_isIso]
  show Scheme.Hom.finrank (Spec.map (CommRingCat.ofHom (algebraMap S (ι → S)))) s = _
  rw [Scheme.Hom.finrank_SpecMap_algebraMap S (ι → S) s, Module.rankAtStalk_eq_finrank_of_free]
  show Module.finrank S (ι → S) = Nat.card ι
  rw [Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

end Finiteness

end ConstExtraLevelBaseSol
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_iff_exists_sectionAt_eq.ConstExtraLevelBaseSol"

open ConstExtraLevelBaseSol in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S : Type} [CommRing S] (E : FakeEllipticCurve Λ N S) (ℓ : ℕ) [NeZero ℓ]
    (W : ZMod ℓ × ZMod ℓ → SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f)
    (hW_add : ∀ i j : ZMod ℓ × ZMod ℓ, W (i + j) = E.L.mul (𝟙 (Spec (CommRingCat.of S))) (W i) (W j))
    (hW_stable : ∀ (x : ↥Λ) (i : ZMod ℓ × ZMod ℓ), ∃ j : ZMod ℓ × ZMod ℓ, pushPt (E.act x) (E.act_over x) (W i) = W j)
    (hW_inj : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (i j : ZMod ℓ × ZMod ℓ),
      FakeEllipticCurve.sectionAt (W i) k sk = FakeEllipticCurve.sectionAt (W j) k sk → i = j)
    (hW_lev : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (i : ZMod ℓ × ZMod ℓ),
      FactorsThrough E.lev (FakeEllipticCurve.sectionAt (W i) k sk) → i = 0) :
    ∃ K : E.ExtraLevel ℓ,
      (∀ i : ZMod ℓ × ZMod ℓ, FactorsThrough K.levK (W i)) ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (Q : SchemeHomOver (geomPoint k sk) E.f),
        FactorsThrough K.levK Q ↔ ∃ i : ZMod ℓ × ZMod ℓ, FakeEllipticCurve.sectionAt (W i) k sk = Q := by
  haveI : Fintype (ZMod ℓ) := ZMod.fintype ℓ
  have hcard : Nat.card (ZMod ℓ × ZMod ℓ) = ℓ ^ 2 := by
    rw [Nat.card_prod, Nat.card_zmod, pow_two]

  have hlev' : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (i : ZMod ℓ × ZMod ℓ),
      FactorsThrough E.lev (FakeEllipticCurve.sectionAt (W i) k sk) → W i = E.L.one _ := by
    intro k _ _ sk i hi
    rw [hW_lev k sk i hi]
    exact W_zero hW_add
  haveI := isClosedImmersion_levK W hW_inj
  refine ⟨{ K := KW S (ZMod ℓ × ZMod ℓ)
            levK := levK W
            levK_closed := inferInstance
            levK_sub := fun t P Q hP hQ => ⟨levK_mul (fun i j => i + j) (fun i j => (hW_add i j).symm) t P Q hP hQ,
              factorsThrough_of_unary t (fun t' P => E.L.inv t' P) (fun t' U P => inv_natural E.L _ _ _ _ P)
                (fun t' w => constPt_inv t' w) (fun i => -i) (fun i => W_neg hW_add i) P hP⟩
            levK_one := fun t => by rw [← constPt_one, ← W_zero hW_add]; exact factorsThrough_constPt t 0
            levK_torsion := fun t P hP => levK_nsmul (fun i => W_torsion hW_add i) t P hP
            levK_stable := fun x _ t P hP =>
              factorsThrough_of_unary t (fun t' P => pushPt (E.act x) (E.act_over x) P) (fun t' U P => rfl)
                (fun t' w => constPt_act t' x w) (fun i => (hW_stable x i).choose)
                (fun i => (hW_stable x i).choose_spec) P hP
            levK_disjoint := fun t P hP hC => levK_disjoint hlev' t P hP hC
            levK_finite := by rw [levK_f]; exact isFinite_πK
            levK_flat := by rw [levK_f]; exact flat_πK
            levK_finitePresentation := by rw [levK_f]; exact locallyOfFinitePresentation_πK
            levK_rank := fun s => by
              haveI : IsFinite (πK S (ZMod ℓ × ZMod ℓ)) := isFinite_πK
              haveI : Flat (πK S (ZMod ℓ × ZMod ℓ)) := flat_πK
              rw [levK_f, finrank_πK, hcard]
            levK_fibre := ?_ }, ?_, ?_⟩
  ·
    intro k _ _ sk _
    let g := geomPoint (S := S) k sk
    have hbij : Function.Bijective fun i : ZMod ℓ × ZMod ℓ =>
        (⟨constPt g (W i), factorsThrough_constPt g i⟩ : {P : SchemeHomOver g E.f // FactorsThrough (levK W) P}) := by
      refine ⟨fun i j h => hW_inj k sk i j (congrArg Subtype.val h), fun P => ?_⟩
      obtain ⟨i, hi⟩ := exists_eq_constPt_of_subsingleton P.1 P.2
      exact ⟨i, Subtype.ext hi.symm⟩
    refine ⟨Equiv.ofBijective _ hbij, fun x y => ?_⟩
    simp only [Equiv.ofBijective_apply]
    rw [hW_add, constPt_mul]
  ·
    intro i
    rw [← constPt_id (W i)]
    exact factorsThrough_constPt _ i
  ·
    intro k _ _ sk Q
    constructor
    · intro h
      obtain ⟨i, hi⟩ := exists_eq_constPt_of_subsingleton Q h
      exact ⟨i, hi.symm⟩
    · rintro ⟨i, rfl⟩
      exact factorsThrough_constPt (W := W) (geomPoint k sk) i

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_iff_exists_sectionAt_eq.ConstExtraLevelBaseSol"

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_iff_exists_sectionAt_eq
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_iff_exists_sectionAt_eq (solution)
