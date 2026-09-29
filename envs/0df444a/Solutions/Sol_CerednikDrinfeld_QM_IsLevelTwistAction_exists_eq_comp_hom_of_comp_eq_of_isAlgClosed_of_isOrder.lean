-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsLevelTwistAction.exists_eq_comp_hom_of_comp_eq_of_isAlgClosed_of_isOrder
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/f140207b-c55f-57ee-95fb-cecdbbcf5877

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsLevelTwistAction_exists_eq_comp_hom_of_comp_eq_of_isAlgClosed_of_isOrder

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

namespace C2Aux

open GoodReductionJacobian

universe u

variable {R : Type u} [CommRing R]

theorem one_natural {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') :
    schemeHomOverComp ψ hψ (L.one t) = L.one t' := by
  set c := schemeHomOverComp ψ hψ (L.one t) with hc
  have hcc : L.mul t' c c = c := by
    rw [hc, ← L.mul_natural t t' ψ hψ, L.one_mul]
  calc c = L.mul t' (L.one t') c := (L.one_mul t' c).symm
    _ = L.mul t' (L.mul t' (L.inv t' c) c) c := by rw [L.inv_mul_cancel]
    _ = L.mul t' (L.inv t' c) (L.mul t' c c) := by rw [L.mul_assoc]
    _ = L.one t' := by rw [hcc, L.inv_mul_cancel]

theorem eq_one_of_mul_eq {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (hc : L.IsCommutative)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (Z Q : SchemeHomOver t f) (h : L.mul t Z Q = Q) : Z = L.one t := by
  have h' : L.mul t Q Z = Q := by rw [hc.mul_comm]; exact h
  calc Z = L.mul t (L.one t) Z := (L.one_mul t Z).symm
    _ = L.mul t (L.mul t (L.inv t Q) Q) Z := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.inv t Q) (L.mul t Q Z) := by rw [L.mul_assoc]
    _ = L.one t := by rw [h', L.inv_mul_cancel]

theorem nsmulPt_natural {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (n : ℕ) (X : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (nsmulPt L t n X) = nsmulPt L t' n (schemeHomOverComp ψ hψ X) := by
  induction n with
  | zero => exact one_natural L t t' ψ hψ
  | succ n ih =>
    change schemeHomOverComp ψ hψ (L.mul t (nsmulPt L t n X) X) = L.mul t' (nsmulPt L t' n (schemeHomOverComp ψ hψ X)) (schemeHomOverComp ψ hψ X)
    rw [L.mul_natural, ih]

theorem mapPt_one {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f') (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : mapPt φ hφ (L.one t) = L'.one t := by
  set c := mapPt φ hφ (L.one t) with hc
  have hcc : L'.mul t c c = c := by rw [hc, ← hmul, L.one_mul]
  calc c = L'.mul t (L'.one t) c := (L'.one_mul t c).symm
    _ = L'.mul t (L'.mul t (L'.inv t c) c) c := by rw [L'.inv_mul_cancel]
    _ = L'.mul t (L'.inv t c) (L'.mul t c c) := by rw [L'.mul_assoc]
    _ = L'.one t := by rw [hcc, L'.inv_mul_cancel]

theorem mapPt_nsmulPt {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f') (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (X : SchemeHomOver t f) :
    mapPt φ hφ (nsmulPt L t n X) = nsmulPt L' t n (mapPt φ hφ X) := by
  induction n with
  | zero => exact mapPt_one L L' φ hφ hmul t
  | succ n ih =>
    change mapPt φ hφ (L.mul t (nsmulPt L t n X) X) = L'.mul t (nsmulPt L' t n (mapPt φ hφ X)) (mapPt φ hφ X)
    rw [hmul, ih]

theorem mapPt_inv_mul {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f') (e : A ≅ A') (he : e.hom ≫ f' = f) (he' : e.inv ≫ f = f')
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      mapPt e.hom he (L.mul t P Q) = L'.mul t (mapPt e.hom he P) (mapPt e.hom he Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (X Y : SchemeHomOver t f') :
    mapPt e.inv he' (L'.mul t X Y) = L.mul t (mapPt e.inv he' X) (mapPt e.inv he' Y) := by
  have hXY : ∀ Z : SchemeHomOver t f', mapPt e.hom he (mapPt e.inv he' Z) = Z := by
    intro Z; apply Subtype.ext
    change (Z.1 ≫ e.inv) ≫ e.hom = Z.1
    rw [Category.assoc, e.inv_hom_id, Category.comp_id]
  have hZW : ∀ Z : SchemeHomOver t f, mapPt e.inv he' (mapPt e.hom he Z) = Z := by
    intro Z; apply Subtype.ext
    change (Z.1 ≫ e.hom) ≫ e.inv = Z.1
    rw [Category.assoc, e.hom_inv_id, Category.comp_id]
  have h := hmul t (mapPt e.inv he' X) (mapPt e.inv he' Y)
  rw [hXY, hXY] at h
  rw [← h, hZW]

end C2Aux

open GoodReductionJacobian

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) {N : ℕ} {B : Type} [CommRing B]
    (𝒳 : Scheme.{0}) (f : 𝒳 ⟶ Spec (CommRingCat.of B))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)), FakeEllipticCurve Λ N S → SchemeHomOver s f)
    (h𝒳 : IsCoarseModuli Λ N 𝒳 f pt)
    (n : ℕ) (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of B))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)
    (G : Type) [Group G] (ρ : G →* Aut M) (χ : G → ↥Λ) (hρ : IsLevelTwistAction Λ N n M fM ptF G ρ χ)
    (p : M ⟶ 𝒳)
    (hp_pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (u : FakeEllipticCurve.WithFullLevel Λ N n S),
      (ptF S s u).1 ≫ p = (pt S s u.1).1)
    (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of B))
    (y y' : SchemeHomOver s fM) (hyy' : y.1 ≫ p = y'.1 ≫ p) :
    ∃ g : G, y'.1 = y.1 ≫ (ρ g).hom := by
  classical
  obtain ⟨u, hu⟩ := hM.ptF_surjective k s y
  obtain ⟨u', hu'⟩ := hM.ptF_surjective k s y'
  obtain ⟨E, PL⟩ := u
  obtain ⟨E', PL'⟩ := u'

  have hptE : pt k s E = pt k s E' := by
    apply Subtype.ext
    have h1 := hp_pt k s ⟨E, PL⟩
    have h2 := hp_pt k s ⟨E', PL'⟩
    rw [hu] at h1
    rw [hu'] at h2
    change (pt k s E).1 = (pt k s E').1
    rw [← h1, ← h2]
    exact hyy'
  obtain ⟨e, he, hmul, hact, hlev⟩ := h𝒳.pt_injective k s E E' hptE
  have he' : e.inv ≫ E.f = E'.f := by
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  have hmul' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (X Y : SchemeHomOver t E'.f),
      mapPt e.inv he' (E'.L.mul t X Y) = E.L.mul t (mapPt e.inv he' X) (mapPt e.inv he' Y) :=
    fun t X Y => C2Aux.mapPt_inv_mul E.L E'.L e he he' hmul t X Y

  have hid : geomPoint k (RingHom.id k) = 𝟙 (Spec (CommRingCat.of k)) := by
    change Spec.map (CommRingCat.ofHom (RingHom.id k)) = 𝟙 _
    rw [CommRingCat.ofHom_id]; exact Spec.map_id _
  have secInj : ∀ {A : Scheme.{0}} {g : A ⟶ Spec (CommRingCat.of k)} (X X' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g),
      FakeEllipticCurve.sectionAt X k (RingHom.id k) = FakeEllipticCurve.sectionAt X' k (RingHom.id k) → X = X' := by
    intro A g X X' h
    have h1 : (FakeEllipticCurve.sectionAt X k (RingHom.id k)).1 = (FakeEllipticCurve.sectionAt X' k (RingHom.id k)).1 :=
      congrArg Subtype.val h
    change geomPoint k (RingHom.id k) ≫ X.1 = geomPoint k (RingHom.id k) ≫ X'.1 at h1
    rw [hid, Category.id_comp, Category.id_comp] at h1
    exact Subtype.ext h1
  have sec_mapPt : ∀ {A A' : Scheme.{0}} {g : A ⟶ Spec (CommRingCat.of k)} {g' : A' ⟶ Spec (CommRingCat.of k)}
      (φ : A ⟶ A') (hφ : φ ≫ g' = g) (X : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g),
      FakeEllipticCurve.sectionAt (mapPt φ hφ X) k (RingHom.id k) = mapPt φ hφ (FakeEllipticCurve.sectionAt X k (RingHom.id k)) := by
    intro A A' g g' φ hφ X
    apply Subtype.ext
    change geomPoint k (RingHom.id k) ≫ (X.1 ≫ φ) = (geomPoint k (RingHom.id k) ≫ X.1) ≫ φ
    rw [Category.assoc]
  have sec_one : ∀ (F : FakeEllipticCurve Λ N k),
      FakeEllipticCurve.sectionAt (F.L.one (𝟙 _)) k (RingHom.id k) = F.L.one (geomPoint k (RingHom.id k)) :=
    fun F => C2Aux.one_natural F.L _ _ _ _
  have sec_nsmul : ∀ (F : FakeEllipticCurve Λ N k) (m : ℕ) (X : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) F.f),
      FakeEllipticCurve.sectionAt (nsmulPt F.L (𝟙 _) m X) k (RingHom.id k) =
        nsmulPt F.L (geomPoint k (RingHom.id k)) m (FakeEllipticCurve.sectionAt X k (RingHom.id k)) :=
    fun F m X => C2Aux.nsmulPt_natural F.L _ _ _ _ m X

  have htor'' : nsmulPt E.L (geomPoint k (RingHom.id k)) n (FakeEllipticCurve.sectionAt (mapPt e.inv he' PL'.P) k (RingHom.id k)) =
      E.L.one (geomPoint k (RingHom.id k)) := by
    rw [← sec_nsmul, ← C2Aux.mapPt_nsmulPt E'.L E.L e.inv he' hmul', PL'.torsion, C2Aux.mapPt_one E'.L E.L e.inv he' hmul', sec_one]
  obtain ⟨c, hc⟩ := PL.generates k (RingHom.id k) _ htor''
  have hcP : pushPt (E.act c) (E.act_over c) PL.P = mapPt e.inv he' PL'.P :=
    secInj _ _ (by rw [sec_mapPt]; exact (sec_mapPt (E.act c) (E.act_over c) PL.P).symm.trans hc |> fun h => by rw [← sec_mapPt]; exact hc)

  have htor1 : nsmulPt E'.L (geomPoint k (RingHom.id k)) n (FakeEllipticCurve.sectionAt (mapPt e.hom he PL.P) k (RingHom.id k)) =
      E'.L.one (geomPoint k (RingHom.id k)) := by
    rw [← sec_nsmul, ← C2Aux.mapPt_nsmulPt E.L E'.L e.hom he hmul, PL.torsion, C2Aux.mapPt_one E.L E'.L e.hom he hmul, sec_one]
  obtain ⟨d, hd⟩ := PL'.generates k (RingHom.id k) _ htor1
  have hdP : pushPt (E'.act d) (E'.act_over d) PL'.P = mapPt e.hom he PL.P :=
    secInj _ _ (by rw [sec_mapPt (E'.act d), sec_mapPt e.hom]; exact hd)

  have hA : PL'.P.1 = (PL.P.1 ≫ E.act c) ≫ e.hom := by
    have h0 : PL.P.1 ≫ E.act c = PL'.P.1 ≫ e.inv := congrArg Subtype.val hcP
    rw [h0, Category.assoc, e.inv_hom_id, Category.comp_id]
  have hB : PL'.P.1 ≫ E'.act d = PL.P.1 ≫ e.hom := congrArg Subtype.val hdP

  have hdc : (d : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]) ∈ Λ := hΛ.mul_mem d.2 c.2
  have hcd : (c : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]) ∈ Λ := hΛ.mul_mem c.2 d.2
  have hC : PL.P.1 ≫ E.act ⟨_, hdc⟩ = PL.P.1 := by
    rw [E.act_mul d c hdc]
    have h1 : (PL.P.1 ≫ (E.act c ≫ E.act d)) ≫ e.hom = PL.P.1 ≫ e.hom := by
      rw [← hB, hA]; simp only [Category.assoc]; rw [hact d]
    exact (cancel_mono e.hom).mp h1
  have hD : PL'.P.1 ≫ E'.act ⟨_, hcd⟩ = PL'.P.1 := by
    rw [E'.act_mul c d hcd, ← Category.assoc, hB, Category.assoc, ← hact c, ← Category.assoc, ← hA]

  have h1Λ : (1 : ℍ[ℚ, a, b]) ∈ Λ := hΛ.one_mem
  have ann : ∀ (F : FakeEllipticCurve Λ N k) (PLF : F.FullLevel n) (x : ↥Λ), PLF.P.1 ≫ F.act x = PLF.P.1 →
      ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) - 1 = (n : ℚ) • (y : ℍ[ℚ, a, b]) := by
    intro F PLF x hx
    let z : ↥Λ := ⟨(x : ℍ[ℚ, a, b]) - 1, Λ.sub_mem x.2 h1Λ⟩
    have hxz : z + ⟨1, h1Λ⟩ = x := Subtype.ext (sub_add_cancel _ _)
    set S := FakeEllipticCurve.sectionAt PLF.P k (RingHom.id k) with hS
    have hone : pushPt (F.act ⟨1, h1Λ⟩) (F.act_over ⟨1, h1Λ⟩) S = S := by
      apply Subtype.ext
      change S.1 ≫ F.act ⟨1, h1Λ⟩ = S.1
      rw [F.act_one h1Λ, Category.comp_id]
    have hQ : pushPt (F.act (z + ⟨1, h1Λ⟩)) (F.act_over (z + ⟨1, h1Λ⟩)) S = S := by
      apply Subtype.ext
      change (geomPoint k (RingHom.id k) ≫ PLF.P.1) ≫ F.act (z + ⟨1, h1Λ⟩) = geomPoint k (RingHom.id k) ≫ PLF.P.1
      rw [hxz, Category.assoc, hx]
    rw [F.act_add, hone] at hQ
    have hz := C2Aux.eq_one_of_mul_eq F.L F.comm _ _ _ hQ
    obtain ⟨y, hy⟩ := (PLF.annihilator k (RingHom.id k) z).mp hz
    exact ⟨y, hy⟩
  obtain ⟨y₁, hy₁⟩ := ann E PL ⟨_, hdc⟩ hC
  obtain ⟨y₂, hy₂⟩ := ann E' PL' ⟨_, hcd⟩ hD
  obtain ⟨g, y₃, hy₃⟩ := hρ.label_surjective c d ⟨y₂, hy₂⟩ ⟨y₁, hy₁⟩

  have hw : ((n : ℚ) • (y₃ : ℍ[ℚ, a, b])) ∈ Λ := by
    rw [Nat.cast_smul_eq_nsmul]; exact Λ.smul_mem _ y₃.2
  have hχ : χ g = c + ⟨_, hw⟩ := Subtype.ext (by change (χ g : ℍ[ℚ, a, b]) = c + (n : ℚ) • (y₃ : ℍ[ℚ, a, b]); rw [← hy₃]; abel)
  have hwP : pushPt (E.act ⟨_, hw⟩) (E.act_over ⟨_, hw⟩) PL.P = E.L.one (𝟙 _) := by
    apply secInj
    rw [sec_mapPt, sec_one]
    exact (PL.annihilator k (RingHom.id k) ⟨_, hw⟩).mpr ⟨y₃, rfl⟩
  have hχP : pushPt (E.act (χ g)) (E.act_over (χ g)) PL.P = pushPt (E.act c) (E.act_over c) PL.P := by
    rw [hχ, E.act_add, hwP, E.L.mul_one]

  have htw : FakeEllipticCurve.WithFullLevel.IsTwist (χ g) (⟨E, PL⟩ : FakeEllipticCurve.WithFullLevel Λ N n k) ⟨E', PL'⟩ := by
    refine ⟨e, he, hmul, hact, hlev, ?_⟩
    apply Subtype.ext
    change ((pushPt (E.act (χ g)) (E.act_over (χ g)) PL.P).1) ≫ e.hom = PL'.P.1
    rw [hχP, hA]
    rfl
  refine ⟨g, ?_⟩
  have := hρ.twist g k s ⟨E, PL⟩ ⟨E', PL'⟩ htw
  rw [hu, hu'] at this
  exact this

end S_CerednikDrinfeld_QM_IsLevelTwistAction_exists_eq_comp_hom_of_comp_eq_of_isAlgClosed_of_isOrder
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsLevelTwistAction_exists_eq_comp_hom_of_comp_eq_of_isAlgClosed_of_isOrder (solution)
