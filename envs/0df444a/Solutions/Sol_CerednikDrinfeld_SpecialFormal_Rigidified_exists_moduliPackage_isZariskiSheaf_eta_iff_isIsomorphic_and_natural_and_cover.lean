-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.exists_moduliPackage_isZariskiSheaf_eta_iff_isIsomorphic_and_natural_and_cover
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/e4d5e1a5-70fb-50d6-a3df-566d127ed658

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_forall_isSpecial_map_and_hasHeight_four_map_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsAdmissible_map_ringHom
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsIsomorphic_map_ringHom
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isIsomorphic_of_forall_isIsomorphic_map_localizationAway
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_X_eq_and_isAdmissible_of_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_FormalODModule_IsSpecial_map
import Theorems.Thm_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_moduliPackage_isZariskiSheaf_eta_iff_isIsomorphic_and_natural_and_cover
p2m_attr_erase "instance" "MvFormalGroup.CartierModule.instAddCommGroup MvFormalGroup.CartierModule.instNeg MvFormalGroup.CartierModule.instAdd MvFormalGroup.CartierModule.instZero MvFormalGroup.WittLaw.instTendstoCofiniteProdMk MvFormalGroup.CartierModule.instModuleWittVector instTopologicallyFGOfFiniteType MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup CerednikDrinfeld.LubinTate.instIsCommMap CerednikDrinfeld.LubinTate.instFintypeGaloisFieldTwo CerednikDrinfeld.LubinTate.sigma_isComm CerednikDrinfeld.LubinTate.sigmaBar_isComm CerednikDrinfeld.BoxBasisLemma.instDecidableInBox CerednikDrinfeld.Standard.law_isComm"
p2m_attr_erase "simp" "MvFormalGroup.CartierModule.toPowerSeries_sub MvFormalGroup.WittLaw.verFam_zero MvFormalGroup.WittLaw.verFam_succ MvFormalGroup.CartierModule.toPowerSeries_frobenius MvFormalGroup.CartierModule.toPowerSeries_verschiebung MvFormalGroup.WittLaw.blk_apply MvFormalGroup.WittLaw.weight_apply MvFormalGroup.CartierModule.toPowerSeries_map MvFormalGroup.CartierModule.toPowerSeries_precompFun MvFormalGroup.CartierModule.toPowerSeries_mapFun MvFormalGroup.CartierModule.mk.injEq MvFormalGroup.WittLaw.pairFam_apply MvFormalGroup.CartierModule.endAct_apply MvFormalGroup.WittLaw.frobFam_apply MvFormalGroup.CartierModule.toPowerSeries_zero MvFormalGroup.CartierModule.tangent_apply MvFormalGroup.CartierModule.toPowerSeries_precomp MvFormalGroup.CartierModule.Examples.toPowerSeries_addLinear MvFormalGroup.CartierModule.toPowerSeries_add MvFormalGroup.CartierModule.toPowerSeries_neg MvFormalGroup.CartierModule.mk.sizeOf_spec MvFormalGroup.CartierModule.inBlk_apply MvFormalGroup.WittLaw.teichFam_apply MvFormalGroup.CartierModule.toPowerSeries_homothety MvFormalGroup.WittLaw.verPoly_succ MvFormalGroup.WittLaw.xVec_coeff MvFormalGroup.WittLaw.cVec_coeff MvFormalGroup.WittLaw.cVec_mul MvFormalGroup.WittLaw.mulFam_apply MvFormalGroup.CartierModule.mapLinear_apply MvFormalGroup.WittLaw.cVec_add MvFormalGroup.WittLaw.cVec_zero MvFormalGroup.WittLaw.verPoly_zero MvFormalGroup.CartierModule.toPowerSeries_wittSMul MvFormalGroup.CartierModule.toPowerSeries_smul_witt MvFormalGroup.WittLaw.cVec_one MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt"
p2m_attr_erase "simp" "MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec CerednikDrinfeld.Standard.emb_inr CerednikDrinfeld.BoxBasisLemma.toFinsupp_apply CerednikDrinfeld.Standard.chi_zero CerednikDrinfeld.Standard.emb_inl CerednikDrinfeld.Standard.chi_one"

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u v

set_option autoImplicit false

noncomputable section

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

namespace KcR4S211
namespace Sheafify

section nilp
variable {p : ℕ}

theorem nilp_of {B Q : Type u} [CommRing B] [CommRing Q] (g : B →+* Q) (hB : IsNilpotent (p : B)) :
    IsNilpotent (p : Q) := by
  obtain ⟨n, hn⟩ := hB
  exact ⟨n, by rw [← map_natCast g p, ← map_pow, hn, map_zero]⟩

theorem nilp_loc {B : Type u} [CommRing B] (hB : IsNilpotent (p : B)) (x : B) :
    IsNilpotent (p : Localization.Away x) :=
  nilp_of (algebraMap B (Localization.Away x)) hB

end nilp

variable {p : ℕ} [Fact p.Prime] {O : Type v} [CommRing O]

structure IsoPkg (p : ℕ) [Fact p.Prime] (O : Type v) [CommRing O]
    extends ModuliPackage.{u, v} p O where
  Iso : ∀ {B : Type u} [CommRing B] {ψ : O →+* B} {hB : IsNilpotent (p : B)},
    obj B ψ hB → obj B ψ hB → Prop
  Good : ∀ {B : Type u} [CommRing B] {ψ : O →+* B} {hB : IsNilpotent (p : B)}, obj B ψ hB → Prop
  good_map : ∀ {B B' : Type u} [CommRing B] [CommRing B'] {ψ : O →+* B} {ψ' : O →+* B'}
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B') (hf : f.comp ψ = ψ')
    (x : obj B ψ hB), Good x → Good (map hB hB' f hf x)
  iso_map : ∀ {B B' : Type u} [CommRing B] [CommRing B'] {ψ : O →+* B} {ψ' : O →+* B'}
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B') (hf : f.comp ψ = ψ')
    (x y : obj B ψ hB), Good x → Good y → Iso x y → Iso (map hB hB' f hf x) (map hB hB' f hf y)
  iso_refl : ∀ {B : Type u} [CommRing B] {ψ : O →+* B} {hB : IsNilpotent (p : B)}
    (x : obj B ψ hB), Good x → Iso x x
  iso_symm : ∀ {B : Type u} [CommRing B] {ψ : O →+* B} {hB : IsNilpotent (p : B)}
    (x y : obj B ψ hB), Good x → Good y → Iso x y → Iso y x
  iso_trans : ∀ {B : Type u} [CommRing B] {ψ : O →+* B} {hB : IsNilpotent (p : B)}
    (x y z : obj B ψ hB), Good x → Good y → Good z → Iso x y → Iso y z → Iso x z

namespace IsoPkg

variable (P : IsoPkg.{u, v} p O)

theorem map_congr {B B' : Type u} [CommRing B] [CommRing B'] {ψ : O →+* B} {ψ' : O →+* B'}
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) {f f' : B →+* B'} (e : f = f')
    (hf : f.comp ψ = ψ') (hf' : f'.comp ψ = ψ') (x : P.obj B ψ hB) :
    P.map hB hB' f hf x = P.map hB hB' f' hf' x := by
  subst e; rfl

def SeparatedAt (B : Type u) [CommRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)) : Prop :=
  ∀ (x y : P.obj B ψ hB), P.Good x → P.Good y →
    ∀ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ →
      (∀ i, P.Iso (P.map hB (nilp_loc hB (f i)) (algebraMap B (Localization.Away (f i))) rfl x)
                  (P.map hB (nilp_loc hB (f i)) (algebraMap B (Localization.Away (f i))) rfl y)) →
      P.Iso x y

def Separated : Prop :=
  ∀ (B : Type u) [CommRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)), P.SeparatedAt B ψ hB

theorem lift_comp_comp {B S Q : Type u} [CommRing B] [CommRing S] [CommRing Q] [Algebra B S]
    (x : B) [IsLocalization.Away x S] {ψ : O →+* B} {ψQ : O →+* Q} (g : B →+* Q)
    (hg : g.comp ψ = ψQ) (hu : IsUnit (g x)) :
    (IsLocalization.Away.lift x hu : S →+* Q).comp ((algebraMap B S).comp ψ) = ψQ := by
  rw [← RingHom.comp_assoc, IsLocalization.Away.lift_comp, hg]

structure Germ (B : Type u) [CommRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)) where
  n : ℕ
  f : Fin n → B
  span_eq : Ideal.span (Set.range f) = ⊤
  t : ∀ i, P.obj (Localization.Away (f i)) ((algebraMap B (Localization.Away (f i))).comp ψ)
    (nilp_loc hB (f i))
  good : ∀ i, P.Good (t i)
  compat : ∀ (i j : Fin n) (Q : Type u) [CommRing Q] (g : B →+* Q)
    (hi : IsUnit (g (f i))) (hj : IsUnit (g (f j))),
    P.Iso (P.map (nilp_loc hB (f i)) (nilp_of g hB) (IsLocalization.Away.lift (f i) hi)
            (lift_comp_comp (f i) g rfl hi) (t i))
          (P.map (nilp_loc hB (f j)) (nilp_of g hB) (IsLocalization.Away.lift (f j) hj)
            (lift_comp_comp (f j) g rfl hj) (t j))

namespace Germ

variable {P}
variable {B : Type u} [CommRing B] {ψ : O →+* B} {hB : IsNilpotent (p : B)}

def restr (G : P.Germ B ψ hB) (i : Fin G.n) {Q : Type u} [CommRing Q] {ψQ : O →+* Q}
    (hQ : IsNilpotent (p : Q)) (g : B →+* Q) (hg : g.comp ψ = ψQ) (hu : IsUnit (g (G.f i))) :
    P.obj Q ψQ hQ :=
  P.map (nilp_loc hB (G.f i)) hQ (IsLocalization.Away.lift (G.f i) hu)
    (lift_comp_comp (G.f i) g hg hu) (G.t i)

theorem restr_congr (G : P.Germ B ψ hB) (i : Fin G.n) {Q : Type u} [CommRing Q] {ψQ : O →+* Q}
    (hQ : IsNilpotent (p : Q)) {g g' : B →+* Q} (e : g = g') (hg : g.comp ψ = ψQ)
    (hg' : g'.comp ψ = ψQ) (hu : IsUnit (g (G.f i))) (hu' : IsUnit (g' (G.f i))) :
    G.restr i hQ g hg hu = G.restr i hQ g' hg' hu' := by
  subst e; rfl

theorem good_restr (G : P.Germ B ψ hB) (i : Fin G.n) {Q : Type u} [CommRing Q] {ψQ : O →+* Q}
    (hQ : IsNilpotent (p : Q)) (g : B →+* Q) (hg : g.comp ψ = ψQ) (hu : IsUnit (g (G.f i))) :
    P.Good (G.restr i hQ g hg hu) :=
  P.good_map _ _ _ _ _ (G.good i)

theorem map_restr (G : P.Germ B ψ hB) (i : Fin G.n) {Q R : Type u} [CommRing Q] [CommRing R]
    {ψQ : O →+* Q} {ψR : O →+* R} (hQ : IsNilpotent (p : Q)) (hR : IsNilpotent (p : R))
    (g : B →+* Q) (hg : g.comp ψ = ψQ) (hu : IsUnit (g (G.f i))) (h : Q →+* R)
    (hh : h.comp ψQ = ψR) :
    P.map hQ hR h hh (G.restr i hQ g hg hu) =
      G.restr i hR (h.comp g) (by rw [RingHom.comp_assoc, hg, hh]) (hu.map h) := by
  unfold restr
  rw [← P.map_comp]
  apply P.map_congr
  apply IsLocalization.ringHom_ext (Submonoid.powers (G.f i))
  rw [RingHom.comp_assoc, IsLocalization.Away.lift_comp, IsLocalization.Away.lift_comp]

theorem restr_iso (G : P.Germ B ψ hB) (i j : Fin G.n) {Q : Type u} [CommRing Q] {ψQ : O →+* Q}
    (hQ : IsNilpotent (p : Q)) (g : B →+* Q) (hg : g.comp ψ = ψQ) (hi : IsUnit (g (G.f i)))
    (hj : IsUnit (g (G.f j))) :
    P.Iso (G.restr i hQ g hg hi) (G.restr j hQ g hg hj) := by
  subst hg
  exact G.compat i j Q g hi hj

theorem restr_iso_of_eq (G : P.Germ B ψ hB) (i : Fin G.n) {Q : Type u} [CommRing Q] {ψQ : O →+* Q}
    (hQ : IsNilpotent (p : Q)) {g g' : B →+* Q} (e : g = g') (hg : g.comp ψ = ψQ)
    (hg' : g'.comp ψ = ψQ) (hu : IsUnit (g (G.f i))) (hu' : IsUnit (g' (G.f i))) :
    P.Iso (G.restr i hQ g hg hu) (G.restr i hQ g' hg' hu') := by
  subst e
  exact P.iso_refl _ (G.good_restr _ _ _ _ _)

theorem restr_self (G : P.Germ B ψ hB) (i : Fin G.n) :
    G.restr i (nilp_loc hB (G.f i)) (algebraMap B (Localization.Away (G.f i))) rfl
      (IsLocalization.Away.algebraMap_isUnit (G.f i)) = G.t i := by
  unfold restr
  have e : (IsLocalization.Away.lift (G.f i)
      (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (G.f i)) (G.f i)) :
        Localization.Away (G.f i) →+* Localization.Away (G.f i)) = RingHom.id _ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (G.f i))
    rw [IsLocalization.Away.lift_comp, RingHom.id_comp]
  rw [P.map_congr _ _ e _ (RingHom.id_comp _), P.map_id]

theorem map_restr' (G : P.Germ B ψ hB) (i : Fin G.n) {Q R : Type u} [CommRing Q] [CommRing R]
    {ψQ : O →+* Q} {ψR : O →+* R} (hQ : IsNilpotent (p : Q)) (hR : IsNilpotent (p : R))
    (g : B →+* Q) (hg : g.comp ψ = ψQ) (hu : IsUnit (g (G.f i))) (h : Q →+* R)
    (hh : h.comp ψQ = ψR) (k : B →+* R) (hk : k.comp ψ = ψR) (e : h.comp g = k)
    (hu' : IsUnit (k (G.f i))) :
    P.map hQ hR h hh (G.restr i hQ g hg hu) = G.restr i hR k hk hu' := by
  rw [map_restr]
  exact G.restr_congr i hR e _ _ _ _

theorem push_iso {G G' : P.Germ B ψ hB} {i : Fin G.n} {j : Fin G'.n} {Q R : Type u}
    [CommRing Q] [CommRing R] {ψQ : O →+* Q} {ψR : O →+* R} {hQ : IsNilpotent (p : Q)}
    (hR : IsNilpotent (p : R)) {g : B →+* Q} {hg : g.comp ψ = ψQ} {hi : IsUnit (g (G.f i))}
    {hj : IsUnit (g (G'.f j))}
    (hiso : P.Iso (G.restr i hQ g hg hi) (G'.restr j hQ g hg hj))
    (h : Q →+* R) (hh : h.comp ψQ = ψR) (k : B →+* R) (hk : k.comp ψ = ψR) (e : h.comp g = k)
    (hi' : IsUnit (k (G.f i))) (hj' : IsUnit (k (G'.f j))) :
    P.Iso (G.restr i hR k hk hi') (G'.restr j hR k hk hj') := by
  have := P.iso_map hQ hR h hh _ _ (G.good_restr _ _ _ _ _) (G'.good_restr _ _ _ _ _) hiso
  rwa [G.map_restr' i hQ hR g hg hi h hh k hk e hi', G'.map_restr' j hQ hR g hg hj h hh k hk e hj']
    at this

theorem isUnit_algebraMap_mul_left {x y b : B}
    (hb : IsUnit (algebraMap B (Localization.Away x) b)) :
    IsUnit (algebraMap B (Localization.Away (x * y)) b) := by
  rw [IsLocalization.Away.algebraMap_isUnit_iff x] at hb
  rw [IsLocalization.Away.algebraMap_isUnit_iff (x * y)]
  obtain ⟨n, hn⟩ := hb
  exact ⟨n, hn.trans (by rw [mul_pow]; exact dvd_mul_right _ _)⟩

theorem isUnit_algebraMap_mul_right {x y b : B}
    (hb : IsUnit (algebraMap B (Localization.Away y) b)) :
    IsUnit (algebraMap B (Localization.Away (x * y)) b) := by
  rw [mul_comm]; exact isUnit_algebraMap_mul_left hb

omit [Fact p.Prime] in
theorem span_range_mul_eq_top {m m' : ℕ} {h : Fin m → B} {h' : Fin m' → B}
    (H : Ideal.span (Set.range h) = ⊤) (H' : Ideal.span (Set.range h') = ⊤) :
    Ideal.span (Set.range fun e : Fin (m * m') =>
      h (finProdFinEquiv.symm e).1 * h' (finProdFinEquiv.symm e).2) = ⊤ := by
  have key : Ideal.span (Set.range h) * Ideal.span (Set.range h') ≤
      Ideal.span (Set.range fun e : Fin (m * m') =>
        h (finProdFinEquiv.symm e).1 * h' (finProdFinEquiv.symm e).2) := by
    rw [Ideal.span_mul_span']
    apply Ideal.span_mono
    rintro _ ⟨_, ⟨c, rfl⟩, _, ⟨d, rfl⟩, rfl⟩
    exact ⟨finProdFinEquiv (c, d), by simp⟩
  rw [H, H', Ideal.top_mul] at key
  exact top_le_iff.mp key

def map (G : P.Germ B ψ hB) {B' : Type u} [CommRing B'] {ψ' : O →+* B'}
    (hB' : IsNilpotent (p : B')) (φ : B →+* B') (hf : φ.comp ψ = ψ') : P.Germ B' ψ' hB' where
  n := G.n
  f := fun i => φ (G.f i)
  span_eq := by
    rw [show (fun i => φ (G.f i)) = φ ∘ G.f from rfl, Set.range_comp, ← Ideal.map_span,
      G.span_eq, Ideal.map_top]
  t := fun i => G.restr i (nilp_loc hB' (φ (G.f i)))
    ((algebraMap B' (Localization.Away (φ (G.f i)))).comp φ)
    (by rw [RingHom.comp_assoc, hf]) (IsLocalization.Away.algebraMap_isUnit (φ (G.f i)))
  good := fun i => G.good_restr _ _ _ _ _
  compat := fun i j Q _ g hi hj => by
    have e : ∀ (x : B) (hx : IsUnit (g (φ x))),
        (IsLocalization.Away.lift (φ x) hx : Localization.Away (φ x) →+* Q).comp
          ((algebraMap B' (Localization.Away (φ x))).comp φ) = g.comp φ := by
      intro x hx
      rw [← RingHom.comp_assoc, IsLocalization.Away.lift_comp]
    rw [G.map_restr' i _ _ _ _ _ _ _ (g.comp φ) (by rw [RingHom.comp_assoc, hf]) (e _ hi) hi,
      G.map_restr' j _ _ _ _ _ _ _ (g.comp φ) (by rw [RingHom.comp_assoc, hf]) (e _ hj) hj]
    exact G.restr_iso i j _ _ _ _ _

theorem map_n (G : P.Germ B ψ hB) {B' : Type u} [CommRing B'] {ψ' : O →+* B'}
    (hB' : IsNilpotent (p : B')) (φ : B →+* B') (hf : φ.comp ψ = ψ') :
    (G.map hB' φ hf).n = G.n := rfl

theorem map_f (G : P.Germ B ψ hB) {B' : Type u} [CommRing B'] {ψ' : O →+* B'}
    (hB' : IsNilpotent (p : B')) (φ : B →+* B') (hf : φ.comp ψ = ψ') (i : Fin G.n) :
    (G.map hB' φ hf).f i = φ (G.f i) := rfl

theorem restr_map (G : P.Germ B ψ hB) {B' : Type u} [CommRing B'] {ψ' : O →+* B'}
    (hB' : IsNilpotent (p : B')) (φ : B →+* B') (hf : φ.comp ψ = ψ') (i : Fin G.n)
    {Q : Type u} [CommRing Q] {ψQ : O →+* Q} (hQ : IsNilpotent (p : Q)) (g : B' →+* Q)
    (hg : g.comp ψ' = ψQ) (hu : IsUnit (g (φ (G.f i)))) :
    (G.map hB' φ hf).restr i hQ g hg hu =
      G.restr i hQ (g.comp φ) (by rw [RingHom.comp_assoc, hf, hg]) hu := by
  exact G.map_restr' i (nilp_loc hB' (φ (G.f i))) hQ
    ((algebraMap B' (Localization.Away (φ (G.f i)))).comp φ)
    (by rw [RingHom.comp_assoc, hf]) (IsLocalization.Away.algebraMap_isUnit (φ (G.f i)))
    (IsLocalization.Away.lift (φ (G.f i)) hu) (lift_comp_comp (φ (G.f i)) g hg hu) (g.comp φ)
    (by rw [RingHom.comp_assoc, hf, hg]) (by rw [← RingHom.comp_assoc, IsLocalization.Away.lift_comp])
    hu

def Agree (G G' : P.Germ B ψ hB) : Prop :=
  ∃ (m : ℕ) (h : Fin m → B) (_ : Ideal.span (Set.range h) = ⊤) (σ : Fin m → Fin G.n)
    (τ : Fin m → Fin G'.n)
    (hσ : ∀ c, IsUnit (algebraMap B (Localization.Away (h c)) (G.f (σ c))))
    (hτ : ∀ c, IsUnit (algebraMap B (Localization.Away (h c)) (G'.f (τ c)))),
    ∀ c, P.Iso (G.restr (σ c) (nilp_loc hB (h c)) (algebraMap B _) rfl (hσ c))
               (G'.restr (τ c) (nilp_loc hB (h c)) (algebraMap B _) rfl (hτ c))

theorem Agree.refl (G : P.Germ B ψ hB) : G.Agree G :=
  ⟨G.n, G.f, G.span_eq, (fun c => c), (fun c => c), fun c => IsLocalization.Away.algebraMap_isUnit _,
    fun c => IsLocalization.Away.algebraMap_isUnit _,
    fun c => P.iso_refl _ (G.good_restr _ _ _ _ _)⟩

theorem Agree.symm {G G' : P.Germ B ψ hB} (H : G.Agree G') : G'.Agree G := by
  obtain ⟨m, h, hh, σ, τ, hσ, hτ, H⟩ := H
  exact ⟨m, h, hh, τ, σ, hτ, hσ, fun c =>
    P.iso_symm _ _ (G.good_restr _ _ _ _ _) (G'.good_restr _ _ _ _ _) (H c)⟩

theorem Agree.trans {G G' G'' : P.Germ B ψ hB} (H₁ : G.Agree G') (H₂ : G'.Agree G'') :
    G.Agree G'' := by
  obtain ⟨m, h, hh, σ, τ, hσ, hτ, H₁⟩ := H₁
  obtain ⟨m', h', hh', σ', τ', hσ', hτ', H₂⟩ := H₂
  refine ⟨m * m', fun e => h (finProdFinEquiv.symm e).1 * h' (finProdFinEquiv.symm e).2,
    span_range_mul_eq_top hh hh', fun e => σ (finProdFinEquiv.symm e).1,
    fun e => τ' (finProdFinEquiv.symm e).2, fun e => isUnit_algebraMap_mul_left (hσ _),
    fun e => isUnit_algebraMap_mul_right (hτ' _), fun e => ?_⟩
  set c := (finProdFinEquiv.symm e).1
  set d := (finProdFinEquiv.symm e).2

  have hτc : IsUnit (algebraMap B (Localization.Away (h c * h' d)) (G'.f (τ c))) :=
    isUnit_algebraMap_mul_left (hτ c)
  have hσd : IsUnit (algebraMap B (Localization.Away (h c * h' d)) (G'.f (σ' d))) :=
    isUnit_algebraMap_mul_right (hσ' d)
  have u₁ : IsUnit (algebraMap B (Localization.Away (h c * h' d)) (h c)) :=
    isUnit_algebraMap_mul_left (IsLocalization.Away.algebraMap_isUnit (h c))
  have u₃ : IsUnit (algebraMap B (Localization.Away (h c * h' d)) (h' d)) :=
    isUnit_algebraMap_mul_right (IsLocalization.Away.algebraMap_isUnit (h' d))
  have l₁ := push_iso (nilp_loc hB (h c * h' d)) (H₁ c)
    (IsLocalization.Away.lift (S := Localization.Away (h c)) (h c) u₁)
    (lift_comp_comp (h c) (algebraMap B _) rfl u₁)
    (algebraMap B _) rfl (IsLocalization.Away.lift_comp _ _)
    (isUnit_algebraMap_mul_left (hσ c)) hτc
  have l₃ := push_iso (nilp_loc hB (h c * h' d)) (H₂ d)
    (IsLocalization.Away.lift (S := Localization.Away (h' d)) (h' d) u₃)
    (lift_comp_comp (h' d) (algebraMap B _) rfl u₃)
    (algebraMap B _) rfl (IsLocalization.Away.lift_comp _ _)
    hσd (isUnit_algebraMap_mul_right (hτ' d))
  have l₂ := G'.restr_iso (τ c) (σ' d) (nilp_loc hB (h c * h' d)) (algebraMap B _) rfl hτc hσd
  exact P.iso_trans _ _ _ (G.good_restr _ _ _ _ _) (G'.good_restr _ _ _ _ _)
    (G''.good_restr _ _ _ _ _)
    (P.iso_trans _ _ _ (G.good_restr _ _ _ _ _) (G'.good_restr _ _ _ _ _)
      (G'.good_restr _ _ _ _ _) l₁ l₂) l₃

theorem Agree.map {G G' : P.Germ B ψ hB} (H : G.Agree G') {B' : Type u} [CommRing B']
    {ψ' : O →+* B'} (hB' : IsNilpotent (p : B')) (φ : B →+* B') (hf : φ.comp ψ = ψ') :
    (G.map hB' φ hf).Agree (G'.map hB' φ hf) := by
  obtain ⟨m, h, hh, σ, τ, hσ, hτ, H⟩ := H
  have hunit : ∀ {x b : B}, IsUnit (algebraMap B (Localization.Away x) b) →
      IsUnit (algebraMap B' (Localization.Away (φ x)) (φ b)) := by
    intro x b hb
    rw [IsLocalization.Away.algebraMap_isUnit_iff x] at hb
    rw [IsLocalization.Away.algebraMap_isUnit_iff (φ x)]
    obtain ⟨n, hn⟩ := hb
    exact ⟨n, by rw [← map_pow]; exact map_dvd φ hn⟩
  refine ⟨m, fun c => φ (h c), ?_, σ, τ, fun c => hunit (hσ c), fun c => hunit (hτ c), fun c => ?_⟩
  · rw [show (fun c => φ (h c)) = φ ∘ h from rfl, Set.range_comp, ← Ideal.map_span, hh,
      Ideal.map_top]
  have hu : IsUnit (((algebraMap B' (Localization.Away (φ (h c)))).comp φ) (h c)) :=
    IsLocalization.Away.algebraMap_isUnit (φ (h c))
  rw [G.restr_map, G'.restr_map]
  exact push_iso (nilp_loc hB' (φ (h c))) (H c)
    (IsLocalization.Away.lift (h c) hu) (lift_comp_comp (h c) _ (by rw [RingHom.comp_assoc, hf]) hu)
    ((algebraMap B' _).comp φ) (by rw [RingHom.comp_assoc, hf]) (IsLocalization.Away.lift_comp _ _)
    _ _

variable (P) in

def setoid (B : Type u) [CommRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)) :
    Setoid (P.Germ B ψ hB) :=
  ⟨Agree, ⟨Agree.refl, Agree.symm, Agree.trans⟩⟩

end Germ

def plus : IsoPkg.{u, v} p O where
  obj B _ ψ hB := Quotient (Germ.setoid P B ψ hB)
  map {B B'} _ _ {ψ ψ'} hB hB' φ hf :=
    Quotient.lift (s := Germ.setoid P B ψ hB)
      (fun G => (Quotient.mk (Germ.setoid P B' ψ' hB') (G.map hB' φ hf)))
      (fun G G' H => Quotient.sound (Germ.Agree.map H hB' φ hf))
  map_id {B} _ {ψ} hB x := by
    induction x using Quotient.ind with | _ G => ?_
    apply Quotient.sound
    refine ⟨G.n, G.f, G.span_eq, (fun c => c), (fun c => c),
      fun c => (show IsUnit (algebraMap B (Localization.Away (G.f c)) (G.f c)) from
        IsLocalization.Away.algebraMap_isUnit (G.f c)),
      fun c => IsLocalization.Away.algebraMap_isUnit _, fun c => ?_⟩
    rw [Germ.restr_map]
    exact G.restr_iso_of_eq c _ (RingHom.comp_id _) _ _ _ _
  map_comp {B B' B''} _ _ _ {ψ ψ' ψ''} hB hB' hB'' g f hf hg x := by
    induction x using Quotient.ind with | _ G => ?_
    apply Quotient.sound
    refine ⟨G.n, fun i => g (f (G.f i)), ?_, (fun c => c), (fun c => c),
      fun c => (show IsUnit (algebraMap B'' (Localization.Away (g (f (G.f c)))) (g (f (G.f c)))) from
        IsLocalization.Away.algebraMap_isUnit _),
      fun c => (show IsUnit (algebraMap B'' (Localization.Away (g (f (G.f c)))) (g (f (G.f c)))) from
        IsLocalization.Away.algebraMap_isUnit _), fun c => ?_⟩
    · exact (G.map hB'' (g.comp f) (by rw [RingHom.comp_assoc, hf, hg])).span_eq
    rw [Germ.restr_map, Germ.restr_map, Germ.restr_map]
    exact G.restr_iso_of_eq c _ (RingHom.comp_assoc _ _ _).symm _ _ _ _
  Iso x y := x = y
  Good _ := True
  good_map _ _ _ _ _ _ := trivial
  iso_map _ _ _ _ _ _ _ _ e := congrArg _ e
  iso_refl _ _ := rfl
  iso_symm _ _ _ _ e := e.symm
  iso_trans _ _ _ _ _ _ e e' := e.trans e'

end IsoPkg

namespace IsoPkg

variable (P : IsoPkg.{u, v} p O)

namespace Germ

variable {P}
variable {B : Type u} [CommRing B] {ψ : O →+* B} {hB : IsNilpotent (p : B)}

theorem restr_congr_idx (G : P.Germ B ψ hB) {i i' : Fin G.n} (e : i = i') {Q : Type u} [CommRing Q]
    {ψQ : O →+* Q} (hQ : IsNilpotent (p : Q)) (g : B →+* Q) (hg : g.comp ψ = ψQ)
    (hu : IsUnit (g (G.f i))) (hu' : IsUnit (g (G.f i'))) :
    G.restr i hQ g hg hu = G.restr i' hQ g hg hu' := by
  subst e; rfl

def single (x : P.obj B ψ hB) (hx : P.Good x) : P.Germ B ψ hB where
  n := 1
  f := fun _ => 1
  span_eq := by simp
  t := fun _ => P.map hB (nilp_loc hB (1 : B)) (algebraMap B (Localization.Away (1 : B))) rfl x
  good := fun _ => P.good_map _ _ _ _ _ hx
  compat := fun i j Q _ g hi hj => P.iso_refl _ (P.good_map _ _ _ _ _ (P.good_map _ _ _ _ _ hx))

theorem single_restr (x : P.obj B ψ hB) (hx : P.Good x) (i : Fin 1) {Q : Type u} [CommRing Q]
    {ψQ : O →+* Q} (hQ : IsNilpotent (p : Q)) (g : B →+* Q) (hg : g.comp ψ = ψQ)
    (hu : IsUnit (g ((single x hx).f i))) :
    (single x hx).restr i hQ g hg hu = P.map hB hQ g hg x := by
  unfold restr single
  dsimp only
  rw [← P.map_comp]
  exact P.map_congr _ _ (IsLocalization.Away.lift_comp _ _) _ _ _

theorem Agree.strong (hsep : P.Separated) {G G' : P.Germ B ψ hB} (H : G.Agree G')
    {T : Type u} [CommRing T] {ψT : O →+* T} (hT : IsNilpotent (p : T)) (κ : B →+* T)
    (hκ : κ.comp ψ = ψT) (i : Fin G.n) (j : Fin G'.n) (hi : IsUnit (κ (G.f i)))
    (hj : IsUnit (κ (G'.f j))) :
    P.Iso (G.restr i hT κ hκ hi) (G'.restr j hT κ hκ hj) := by
  obtain ⟨m, h, hh, σ, τ, hσ, hτ, H⟩ := H
  refine hsep T ψT hT _ _ (G.good_restr _ _ _ _ _) (G'.good_restr _ _ _ _ _) m (fun c => κ (h c))
    (by rw [show (fun c => κ (h c)) = κ ∘ h from rfl, Set.range_comp, ← Ideal.map_span, hh,
      Ideal.map_top]) fun c => ?_

  set Tc := Localization.Away (κ (h c))
  have hTc : IsNilpotent (p : Tc) := nilp_loc hT _
  have u0 : IsUnit (((algebraMap T Tc).comp κ) (h c)) := by
    rw [RingHom.comp_apply]; exact IsLocalization.Away.algebraMap_isUnit _

  let μ : Localization.Away (h c) →+* Tc := IsLocalization.Away.lift (h c) u0
  have hμ : μ.comp (algebraMap B (Localization.Away (h c))) = (algebraMap T Tc).comp κ :=
    IsLocalization.Away.lift_comp _ _
  have uσ : IsUnit (((algebraMap T Tc).comp κ) (G.f (σ c))) := by
    rw [← hμ]; exact (hσ c).map μ
  have uτ : IsUnit (((algebraMap T Tc).comp κ) (G'.f (τ c))) := by
    rw [← hμ]; exact (hτ c).map μ
  have e₀ : ((algebraMap T Tc).comp κ).comp ψ = (algebraMap T Tc).comp ψT := by
    rw [RingHom.comp_assoc, hκ]
  have hi' : IsUnit (((algebraMap T Tc).comp κ) (G.f i)) := by
    rw [RingHom.comp_apply]; exact hi.map _
  have hj' : IsUnit (((algebraMap T Tc).comp κ) (G'.f j)) := by
    rw [RingHom.comp_apply]; exact hj.map _
  rw [G.map_restr' i hT hTc κ hκ hi (algebraMap T Tc) rfl ((algebraMap T Tc).comp κ) e₀ rfl hi',
    G'.map_restr' j hT hTc κ hκ hj (algebraMap T Tc) rfl ((algebraMap T Tc).comp κ) e₀ rfl hj']
  have l₁ := G.restr_iso i (σ c) hTc ((algebraMap T Tc).comp κ) e₀ hi' uσ
  have l₂ := push_iso hTc (H c) μ (by rw [← RingHom.comp_assoc, hμ, RingHom.comp_assoc, hκ])
    ((algebraMap T Tc).comp κ) e₀ hμ uσ uτ
  have l₃ := G'.restr_iso (τ c) j hTc ((algebraMap T Tc).comp κ) e₀ uτ hj'
  exact P.iso_trans _ _ _ (G.good_restr _ _ _ _ _) (G'.good_restr _ _ _ _ _)
    (G'.good_restr _ _ _ _ _)
    (P.iso_trans _ _ _ (G.good_restr _ _ _ _ _) (G.good_restr _ _ _ _ _)
      (G'.good_restr _ _ _ _ _) l₁ l₂) l₃

end Germ

namespace Refine

variable {B : Type u} [CommRing B] {n : ℕ} (f : Fin n → B)
  (L : Fin n → Type u) [∀ i, CommRing (L i)] [∀ i, Algebra B (L i)]
  [∀ i, IsLocalization.Away (f i) (L i)] (m : Fin n → ℕ) (h : ∀ i, Fin (m i) → L i)

def num (i : Fin n) (c : Fin (m i)) : B := (IsLocalization.Away.sec (f i) (h i c)).1

def H (k : Fin (∑ i, m i)) : B :=
  f (finSigmaFinEquiv.symm k).1 * num f L m h (finSigmaFinEquiv.symm k).1 (finSigmaFinEquiv.symm k).2

omit [Fact p.Prime] in
private theorem _root_.KcR4S211.Sheafify.IsoPkg.Refine.span_eq (hf : Ideal.span (Set.range f) = ⊤) (hh : ∀ i, Ideal.span (Set.range (h i)) = ⊤) :
    Ideal.span (Set.range (H f L m h)) = ⊤ := by
  classical

  rw [← Ideal.radical_eq_top, eq_top_iff, ← hf, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  haveI : IsLocalization (Submonoid.powers (f i)) (L i) := inferInstance
  have h₁ : Ideal.span (Set.range (h i)) ≤
      Ideal.span (algebraMap B (L i) '' Set.range (H f L m h)) := by
    rw [Ideal.span_le]
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe, IsLocalization.mem_span_map (Submonoid.powers (f i))]
    refine ⟨f i * num f L m h i c, Ideal.subset_span ⟨finSigmaFinEquiv ⟨i, c⟩, ?_⟩, ?_⟩
    · show H f L m h (finSigmaFinEquiv ⟨i, c⟩) = _
      unfold H
      rw [Equiv.symm_apply_apply]
    · refine ⟨⟨f i ^ ((IsLocalization.Away.sec (f i) (h i c)).2 + 1), _, rfl⟩, ?_⟩
      rw [IsLocalization.eq_mk'_iff_mul_eq]
      show h i c * algebraMap B (L i) (f i ^ ((IsLocalization.Away.sec (f i) (h i c)).2 + 1)) = _
      rw [pow_succ, map_mul, ← mul_assoc, IsLocalization.Away.sec_spec (f i) (h i c), num, ← map_mul,
        mul_comm]
  have h₂ : (1 : L i) ∈ Ideal.span (algebraMap B (L i) '' Set.range (H f L m h)) := by
    apply h₁; rw [hh i]; trivial
  rw [IsLocalization.mem_span_map (Submonoid.powers (f i))] at h₂
  obtain ⟨y, hy, ⟨_, ⟨k, rfl⟩⟩, hyz⟩ := h₂
  rw [IsLocalization.eq_mk'_iff_mul_eq, one_mul] at hyz
  obtain ⟨⟨_, ⟨l, rfl⟩⟩, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers (f i)) (L i)).mp hyz
  dsimp only at hc
  refine ⟨l + k, ?_⟩
  show f i ^ (l + k) ∈ Ideal.span (Set.range (H f L m h))
  rw [pow_add, hc]
  exact Ideal.mul_mem_left _ _ hy

p2m_export "KcR4S211.Sheafify.IsoPkg.Refine" "span_eq"
variable {f L m h}

theorem isUnit_f {T : Type u} [CommRing T] (g : B →+* T) (k : Fin (∑ i, m i))
    (hu : IsUnit (g (H f L m h k))) : IsUnit (g (f (finSigmaFinEquiv.symm k).1)) := by
  unfold H at hu; rw [map_mul] at hu; exact isUnit_of_mul_isUnit_left hu

def lam {T : Type u} [CommRing T] (g : B →+* T) (k : Fin (∑ i, m i))
    (hu : IsUnit (g (H f L m h k))) : L (finSigmaFinEquiv.symm k).1 →+* T :=
  IsLocalization.Away.lift (f (finSigmaFinEquiv.symm k).1) (isUnit_f g k hu)

theorem lam_comp {T : Type u} [CommRing T] (g : B →+* T) (k : Fin (∑ i, m i))
    (hu : IsUnit (g (H f L m h k))) :
    (lam g k hu).comp (algebraMap B (L (finSigmaFinEquiv.symm k).1)) = g :=
  IsLocalization.Away.lift_comp _ _

theorem isUnit_lam_h {T : Type u} [CommRing T] (g : B →+* T) (k : Fin (∑ i, m i))
    (hu : IsUnit (g (H f L m h k))) :
    IsUnit (lam g k hu (h (finSigmaFinEquiv.symm k).1 (finSigmaFinEquiv.symm k).2)) := by
  have hnum : IsUnit (g (num f L m h (finSigmaFinEquiv.symm k).1 (finSigmaFinEquiv.symm k).2)) := by
    unfold H at hu; rw [map_mul] at hu; exact isUnit_of_mul_isUnit_right hu
  have key := congrArg (lam g k hu) (IsLocalization.Away.sec_spec (f (finSigmaFinEquiv.symm k).1)
    (h (finSigmaFinEquiv.symm k).1 (finSigmaFinEquiv.symm k).2))
  rw [map_mul, ← RingHom.comp_apply, ← RingHom.comp_apply, lam_comp] at key
  rw [num] at hnum
  rw [← key] at hnum
  exact isUnit_of_mul_isUnit_left hnum

omit [Fact p.Prime] in
theorem isUnit_H (k : Fin (∑ i, m i)) :
    IsUnit (algebraMap B (Localization.Away (H f L m h k)) (H f L m h k)) :=
  IsLocalization.Away.algebraMap_isUnit _

end Refine

theorem Germ.agree_of_locally {B : Type u} [CommRing B] {ψ : O →+* B} {hB : IsNilpotent (p : B)}
    (G G' : P.Germ B ψ hB) {n : ℕ} (f : Fin n → B) (hf : Ideal.span (Set.range f) = ⊤)
    (L : Fin n → Type u) [∀ i, CommRing (L i)] [∀ i, Algebra B (L i)]
    [∀ i, IsLocalization.Away (f i) (L i)] (hL : ∀ i, IsNilpotent (p : L i))
    (hloc : ∀ i, (G.map (hL i) (algebraMap B (L i)) rfl).Agree (G'.map (hL i) (algebraMap B (L i)) rfl)) :
    G.Agree G' := by
  choose m h hh σ τ hσ hτ hiso using hloc
  refine ⟨∑ i, m i, Refine.H f L m h, Refine.span_eq f L m h hf hh,
    fun k => σ _ (finSigmaFinEquiv.symm k).2, fun k => τ _ (finSigmaFinEquiv.symm k).2,
    fun k => ?_, fun k => ?_, fun k => ?_⟩
  all_goals
    set i := (finSigmaFinEquiv.symm k).1
    set c := (finSigmaFinEquiv.symm k).2
    set T := Localization.Away (Refine.H f L m h k)
    have hu : IsUnit (algebraMap B T (Refine.H f L m h k)) := IsLocalization.Away.algebraMap_isUnit _
    have uh := Refine.isUnit_lam_h (f := f) (L := L) (m := m) (h := h) (algebraMap B T) k hu
    let μ : Localization.Away (h i c) →+* T := IsLocalization.Away.lift (h i c) uh
    have hμ : (μ.comp (algebraMap (L i) (Localization.Away (h i c)))).comp (algebraMap B (L i)) =
        algebraMap B T := by
      rw [show μ.comp (algebraMap (L i) (Localization.Away (h i c))) = Refine.lam (algebraMap B T) k hu
        from IsLocalization.Away.lift_comp _ _]
      exact Refine.lam_comp _ _ _
    have hμb : ∀ b, μ (algebraMap (L i) (Localization.Away (h i c)) (algebraMap B (L i) b)) =
        algebraMap B T b := fun b => by rw [← hμ]; rfl
  · have := (hσ i c).map μ
    rw [Germ.map_f, hμb] at this
    exact this
  · have := (hτ i c).map μ
    rw [Germ.map_f, hμb] at this
    exact this
  · have key := hiso i c
    rw [Germ.restr_map, Germ.restr_map] at key
    exact Germ.push_iso (nilp_loc hB _) key μ
      (by rw [← RingHom.comp_assoc, ← RingHom.comp_assoc, hμ]) (algebraMap B T) rfl
      (by rw [← RingHom.comp_assoc, hμ]) _ _

theorem plus_separated : P.plus.Separated := by
  intro B _ ψ hB x y _ _ n f hf hloc
  induction x using Quotient.ind with | _ G => ?_
  induction y using Quotient.ind with | _ G' => ?_
  apply Quotient.sound
  exact Germ.agree_of_locally P G G' f hf (fun i => Localization.Away (f i)) (fun i => nilp_loc hB (f i))
    fun i => Quotient.exact (s := Germ.setoid P _ _ _) (hloc i)

end IsoPkg

namespace IsoPkg

variable (P : IsoPkg.{u, v} p O)

section Glue

variable {P}
variable {B : Type u} [CommRing B] {ψ : O →+* B} {hB : IsNilpotent (p : B)} {n : ℕ} {f : Fin n → B}
  {L : Fin n → Type u} [∀ i, CommRing (L i)] [∀ i, Algebra B (L i)]
  [∀ i, IsLocalization.Away (f i) (L i)] {hL : ∀ i, IsNilpotent (p : L i)}

variable (hB f) in

def CrossIso (G : ∀ k, P.Germ (L k) ((algebraMap B (L k)).comp ψ) (hL k)) : Prop :=
  ∀ (k₁ k₂ : Fin n) (Q : Type u) [CommRing Q] (g : B →+* Q) (hf₁ : IsUnit (g (f k₁)))
    (hf₂ : IsUnit (g (f k₂))) (a₁ : Fin (G k₁).n) (a₂ : Fin (G k₂).n)
    (hu₁ : IsUnit (IsLocalization.Away.lift (S := L k₁) (f k₁) hf₁ ((G k₁).f a₁)))
    (hu₂ : IsUnit (IsLocalization.Away.lift (S := L k₂) (f k₂) hf₂ ((G k₂).f a₂))),
    P.Iso ((G k₁).restr a₁ (nilp_of g hB) (IsLocalization.Away.lift (f k₁) hf₁)
            (lift_comp_comp (f k₁) g rfl hf₁) hu₁)
          ((G k₂).restr a₂ (nilp_of g hB) (IsLocalization.Away.lift (f k₂) hf₂)
            (lift_comp_comp (f k₂) g rfl hf₂) hu₂)

theorem sigma_restr_congr (G : ∀ k, P.Germ (L k) ((algebraMap B (L k)).comp ψ) (hL k))
    {Q : Type u} [CommRing Q] {ψQ : O →+* Q} (hQ : IsNilpotent (p : Q)) (g : B →+* Q)
    (hg : g.comp ψ = ψQ) {x y : Σ k, Fin (G k).n} (e : x = y)
    (hfx : IsUnit (g (f x.1))) (hfy : IsUnit (g (f y.1)))
    (hux : IsUnit (IsLocalization.Away.lift (S := L x.1) (f x.1) hfx ((G x.1).f x.2)))
    (huy : IsUnit (IsLocalization.Away.lift (S := L y.1) (f y.1) hfy ((G y.1).f y.2))) :
    (G x.1).restr x.2 hQ (IsLocalization.Away.lift (f x.1) hfx) (lift_comp_comp (f x.1) g hg hfx) hux =
      (G y.1).restr y.2 hQ (IsLocalization.Away.lift (f y.1) hfy) (lift_comp_comp (f y.1) g hg hfy)
        huy := by
  subst e; rfl

variable (hB f) in

def glueT (G : ∀ k, P.Germ (L k) ((algebraMap B (L k)).comp ψ) (hL k)) (k' : Fin (∑ k, (G k).n)) :
    P.obj (Localization.Away (Refine.H f L (fun k => (G k).n) (fun k => (G k).f) k'))
      ((algebraMap B _).comp ψ) (nilp_loc hB _) :=
  (G (finSigmaFinEquiv.symm k').1).restr (finSigmaFinEquiv.symm k').2 (nilp_loc hB _)
    (IsLocalization.Away.lift (f (finSigmaFinEquiv.symm k').1)
      (Refine.isUnit_f (algebraMap B _) k'
        (Refine.isUnit_H (f := f) (L := L) (m := fun k => (G k).n) (h := fun k => (G k).f) k')))
    (lift_comp_comp _ _ rfl _)
    (Refine.isUnit_lam_h (algebraMap B _) k'
      (Refine.isUnit_H (f := f) (L := L) (m := fun k => (G k).n) (h := fun k => (G k).f) k'))

theorem glueT_map (G : ∀ k, P.Germ (L k) ((algebraMap B (L k)).comp ψ) (hL k))
    (k' : Fin (∑ k, (G k).n)) {Q : Type u} [CommRing Q] {ψQ : O →+* Q} (hQ : IsNilpotent (p : Q))
    (g : B →+* Q) (hg : g.comp ψ = ψQ)
    (hu : IsUnit (g (Refine.H f L (fun k => (G k).n) (fun k => (G k).f) k'))) :
    P.map (nilp_loc hB _) hQ (IsLocalization.Away.lift _ hu) (lift_comp_comp _ g hg hu)
        (glueT hB f G k') =
      (G (finSigmaFinEquiv.symm k').1).restr (finSigmaFinEquiv.symm k').2 hQ
        (IsLocalization.Away.lift (f (finSigmaFinEquiv.symm k').1) (Refine.isUnit_f g k' hu))
        (lift_comp_comp _ g hg _)
        (Refine.isUnit_lam_h (L := L) (m := fun k => (G k).n) (h := fun k => (G k).f) g k' hu) := by
  unfold glueT
  rw [Germ.map_restr]
  apply Germ.restr_congr
  apply IsLocalization.ringHom_ext (Submonoid.powers (f (finSigmaFinEquiv.symm k').1))
  rw [RingHom.comp_assoc, IsLocalization.Away.lift_comp, IsLocalization.Away.lift_comp,
    IsLocalization.Away.lift_comp]

variable (hB f) in

def glue (hf : Ideal.span (Set.range f) = ⊤)
    (G : ∀ k, P.Germ (L k) ((algebraMap B (L k)).comp ψ) (hL k)) (hX : CrossIso hB f G) :
    P.Germ B ψ hB where
  n := ∑ k, (G k).n
  f := Refine.H f L (fun k => (G k).n) (fun k => (G k).f)
  span_eq := Refine.span_eq f L _ _ hf (fun k => (G k).span_eq)
  t := glueT hB f G
  good := fun k' => Germ.good_restr _ _ _ _ _ _
  compat := fun k₁ k₂ Q _ g h₁ h₂ => by
    rw [glueT_map G k₁ (nilp_of g hB) g rfl h₁, glueT_map G k₂ (nilp_of g hB) g rfl h₂]
    exact hX _ _ Q g _ _ _ _ _ _

theorem glue_n (hf : Ideal.span (Set.range f) = ⊤)
    (G : ∀ k, P.Germ (L k) ((algebraMap B (L k)).comp ψ) (hL k)) (hX : CrossIso hB f G) :
    (glue hB f hf G hX).n = ∑ k, (G k).n := rfl

theorem glue_restr (hf : Ideal.span (Set.range f) = ⊤)
    (G : ∀ k, P.Germ (L k) ((algebraMap B (L k)).comp ψ) (hL k)) (hX : CrossIso hB f G)
    (k' : Fin (∑ k, (G k).n)) {Q : Type u} [CommRing Q] {ψQ : O →+* Q} (hQ : IsNilpotent (p : Q))
    (g : B →+* Q) (hg : g.comp ψ = ψQ)
    (hu : IsUnit (g (Refine.H f L (fun k => (G k).n) (fun k => (G k).f) k'))) :
    (glue hB f hf G hX).restr (k' : Fin (glue hB f hf G hX).n) hQ g hg hu =
      (G (finSigmaFinEquiv.symm k').1).restr (finSigmaFinEquiv.symm k').2 hQ
        (IsLocalization.Away.lift (f (finSigmaFinEquiv.symm k').1) (Refine.isUnit_f g k' hu))
        (lift_comp_comp _ g hg _)
        (Refine.isUnit_lam_h (L := L) (m := fun k => (G k).n) (h := fun k => (G k).f) g k' hu) := by
  unfold Germ.restr glue
  exact glueT_map (hB := hB) G k' hQ g hg hu

end Glue

theorem plus_glue (hsep : P.Separated)
    (B : Type u) [CommRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B))
    (n : ℕ) (f : Fin n → B) (hf : Ideal.span (Set.range f) = ⊤)
    (L : Fin n → Type u) [∀ i, CommRing (L i)] [∀ i, Algebra B (L i)]
    [∀ i, IsLocalization.Away (f i) (L i)]
    (hL : ∀ i, IsNilpotent (p : L i))
    (L₂ : Fin n → Fin n → Type u) [∀ i j, CommRing (L₂ i j)] [∀ i j, Algebra B (L₂ i j)]
    [∀ i j, IsLocalization.Away (f i * f j) (L₂ i j)]
    (hL₂ : ∀ i j, IsNilpotent (p : L₂ i j))
    (l : ∀ i j, L i →+* L₂ i j) (r : ∀ i j, L j →+* L₂ i j)
    (hl : ∀ i j (b : B), l i j (algebraMap B (L i) b) = algebraMap B (L₂ i j) b)
    (hr : ∀ i j (b : B), r i j (algebraMap B (L j) b) = algebraMap B (L₂ i j) b)
    (x : ∀ i, P.plus.obj (L i) ((algebraMap B (L i)).comp ψ) (hL i))
    (hx : ∀ i j, P.plus.map (ψ' := (algebraMap B (L₂ i j)).comp ψ) (hL i) (hL₂ i j) (l i j)
            (RingHom.ext fun b => hl i j (ψ b)) (x i) =
          P.plus.map (ψ' := (algebraMap B (L₂ i j)).comp ψ) (hL j) (hL₂ i j) (r i j)
            (RingHom.ext fun b => hr i j (ψ b)) (x j)) :
    ∃ m : P.plus.obj B ψ hB, ∀ i,
      P.plus.map (ψ' := (algebraMap B (L i)).comp ψ) hB (hL i) (algebraMap B (L i)) rfl m = x i := by
  have hrep : ∀ k, ∃ G : P.Germ (L k) ((algebraMap B (L k)).comp ψ) (hL k),
      Quotient.mk (Germ.setoid P _ _ _) G = x k := fun k => Quotient.exists_rep (x k)
  choose G hG using hrep

  have hX : CrossIso hB f G := by
    intro k₁ k₂ Q _ g hf₁ hf₂ a₁ a₂ hu₁ hu₂
    have h12 : IsUnit (g (f k₁ * f k₂)) := by rw [map_mul]; exact hf₁.mul hf₂
    let ν : L₂ k₁ k₂ →+* Q := IsLocalization.Away.lift (f k₁ * f k₂) h12
    have hν : ν.comp (algebraMap B (L₂ k₁ k₂)) = g := IsLocalization.Away.lift_comp _ _
    have e₁ : ν.comp (l k₁ k₂) = IsLocalization.Away.lift (f k₁) hf₁ := by
      apply IsLocalization.ringHom_ext (Submonoid.powers (f k₁))
      rw [IsLocalization.Away.lift_comp, RingHom.comp_assoc,
        show (l k₁ k₂).comp (algebraMap B (L k₁)) = algebraMap B (L₂ k₁ k₂) from RingHom.ext (hl k₁ k₂), hν]
    have e₂ : ν.comp (r k₁ k₂) = IsLocalization.Away.lift (f k₂) hf₂ := by
      apply IsLocalization.ringHom_ext (Submonoid.powers (f k₂))
      rw [IsLocalization.Away.lift_comp, RingHom.comp_assoc,
        show (r k₁ k₂).comp (algebraMap B (L k₂)) = algebraMap B (L₂ k₁ k₂) from RingHom.ext (hr k₁ k₂), hν]
    have A : ((G k₁).map (ψ' := (algebraMap B (L₂ k₁ k₂)).comp ψ) (hL₂ k₁ k₂) (l k₁ k₂)
          (RingHom.ext fun b => hl k₁ k₂ (ψ b))).Agree
        ((G k₂).map (ψ' := (algebraMap B (L₂ k₁ k₂)).comp ψ) (hL₂ k₁ k₂) (r k₁ k₂)
          (RingHom.ext fun b => hr k₁ k₂ (ψ b))) := by
      apply Quotient.exact (s := Germ.setoid P _ _ _)
      have := hx k₁ k₂
      rw [← hG k₁, ← hG k₂] at this
      exact this
    have hi : IsUnit (ν (((G k₁).map (ψ' := (algebraMap B (L₂ k₁ k₂)).comp ψ) (hL₂ k₁ k₂) (l k₁ k₂)
        (RingHom.ext fun b => hl k₁ k₂ (ψ b))).f a₁)) := by
      rw [Germ.map_f, ← RingHom.comp_apply, e₁]; exact hu₁
    have hj : IsUnit (ν (((G k₂).map (ψ' := (algebraMap B (L₂ k₁ k₂)).comp ψ) (hL₂ k₁ k₂) (r k₁ k₂)
        (RingHom.ext fun b => hr k₁ k₂ (ψ b))).f a₂)) := by
      rw [Germ.map_f, ← RingHom.comp_apply, e₂]; exact hu₂
    have key := A.strong hsep (nilp_of g hB) ν (by rw [← RingHom.comp_assoc, hν]) a₁ a₂ hi hj
    rw [Germ.restr_map, Germ.restr_map,
      (G k₁).restr_congr a₁ _ e₁ _ (lift_comp_comp (f k₁) g rfl hf₁) _ hu₁,
      (G k₂).restr_congr a₂ _ e₂ _ (lift_comp_comp (f k₂) g rfl hf₂) _ hu₂] at key
    exact key
  refine ⟨Quotient.mk _ (glue hB f hf G hX), fun k => ?_⟩
  rw [← hG k]
  apply Quotient.sound

  have hunit : ∀ a : Fin (G k).n, IsUnit (algebraMap (L k) (Localization.Away ((G k).f a))
      (((glue hB f hf G hX).map (hL k) (algebraMap B (L k)) rfl).f
        (finSigmaFinEquiv (n := fun k => (G k).n) ⟨k, a⟩ : Fin (∑ k, (G k).n)))) := by
    intro a
    rw [Germ.map_f]
    show IsUnit (algebraMap (L k) _ (algebraMap B (L k)
      (Refine.H f L (fun k => (G k).n) (fun k => (G k).f) (finSigmaFinEquiv (n := fun k => (G k).n) ⟨k, a⟩))))
    unfold Refine.H
    rw [Equiv.symm_apply_apply]
    dsimp only
    rw [map_mul, map_mul, Refine.num, ← IsLocalization.Away.sec_spec (f k) ((G k).f a), map_mul,
      ← mul_assoc]
    refine IsUnit.mul (IsUnit.mul ?_ (IsLocalization.Away.algebraMap_isUnit _)) ?_
    · exact ((IsLocalization.Away.algebraMap_isUnit (S := L k) (f k)).map
        (algebraMap (L k) (Localization.Away ((G k).f a))))
    · rw [map_pow, map_pow]
      exact ((IsLocalization.Away.algebraMap_isUnit (S := L k) (f k)).map
        (algebraMap (L k) (Localization.Away ((G k).f a)))).pow _
  refine ⟨(G k).n, (G k).f, (G k).span_eq,
    fun a => (finSigmaFinEquiv (n := fun k => (G k).n) ⟨k, a⟩ : Fin (∑ k, (G k).n)), fun a => a, hunit,
    fun a => IsLocalization.Away.algebraMap_isUnit _, fun a => ?_⟩
  set R := Localization.Away ((G k).f a)
  have hfk : IsUnit (((algebraMap (L k) R).comp (algebraMap B (L k))) (f k)) := by
    rw [RingHom.comp_apply]
    exact (IsLocalization.Away.algebraMap_isUnit (S := L k) (f k)).map _
  rw [Germ.restr_map, glue_restr]
  rw [sigma_restr_congr G (nilp_loc (hL k) _) ((algebraMap (L k) R).comp (algebraMap B (L k))) rfl
    (Equiv.symm_apply_apply finSigmaFinEquiv ⟨k, a⟩) _ hfk _
    (by rw [show IsLocalization.Away.lift (f k) hfk = algebraMap (L k) R from
          IsLocalization.ringHom_ext (Submonoid.powers (f k)) (IsLocalization.Away.lift_comp _ _)]
        exact IsLocalization.Away.algebraMap_isUnit _)]
  exact (G k).restr_iso_of_eq a _
    (IsLocalization.ringHom_ext (Submonoid.powers (f k)) (IsLocalization.Away.lift_comp _ _)) _ _ _ _

theorem isZariskiSheaf_plus_plus : P.plus.plus.toModuliPackage.IsZariskiSheaf := by
  intro B _ ψ hB n f hf L _ _ _ hL L₂ _ _ _ hL₂ l r hl hr
  refine ⟨fun m m' hmm' => ?_, fun x hx => P.plus.plus_glue P.plus_separated B ψ hB n f hf L hL L₂ hL₂ l r hl hr x hx⟩

  induction m using Quotient.ind with | _ G => ?_
  induction m' using Quotient.ind with | _ G' => ?_
  apply Quotient.sound
  exact Germ.agree_of_locally P.plus G G' f hf L hL fun i => Quotient.exact (s := Germ.setoid P.plus _ _ _) (hmm' i)

end IsoPkg

namespace IsoPkg

variable (P : IsoPkg.{u, v} p O)

section Eta

variable {P}
variable {B : Type u} [CommRing B] {ψ : O →+* B} {hB : IsNilpotent (p : B)}

theorem Germ.single_map_agree (x : P.obj B ψ hB) (hx : P.Good x) {B' : Type u} [CommRing B']
    {ψ' : O →+* B'} (hB' : IsNilpotent (p : B')) (φ : B →+* B') (hf : φ.comp ψ = ψ') :
    ((Germ.single x hx).map hB' φ hf).Agree
      (Germ.single (P.map hB hB' φ hf x) (P.good_map _ _ _ _ _ hx)) := by
  refine ⟨1, fun _ => 1, by simp, fun _ => (0 : Fin 1), fun _ => (0 : Fin 1),
    fun _ => by rw [Germ.map_f]; show IsUnit (algebraMap B' _ (φ 1)); rw [map_one, map_one]; exact isUnit_one,
    fun _ => by show IsUnit (algebraMap B' _ (1 : B')); rw [map_one]; exact isUnit_one, fun c => ?_⟩
  rw [Germ.restr_map, Germ.single_restr, Germ.single_restr, ← P.map_comp]
  exact P.iso_refl _ (P.good_map _ _ _ _ _ hx)

theorem Germ.single_agree_of_iso (x y : P.obj B ψ hB) (hx : P.Good x) (hy : P.Good y) (h : P.Iso x y) :
    (Germ.single x hx).Agree (Germ.single y hy) := by
  refine ⟨1, fun _ => 1, by simp, fun _ => (0 : Fin 1), fun _ => (0 : Fin 1),
    fun _ => by show IsUnit (algebraMap B _ (1 : B)); rw [map_one]; exact isUnit_one,
    fun _ => by show IsUnit (algebraMap B _ (1 : B)); rw [map_one]; exact isUnit_one, fun c => ?_⟩
  rw [Germ.single_restr, Germ.single_restr]
  exact P.iso_map _ _ _ _ _ _ hx hy h

end Eta

section EtaDef

def BasePt : Type _ :=
  ∀ (B : Type u) [CommRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)), P.obj B ψ hB

variable {P} in

def GoodPt (pt : P.BasePt) : Prop :=
  ∀ (B : Type u) [CommRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)), P.Good (pt B ψ hB)

variable (pt : P.BasePt) (hpt : GoodPt pt)

open Classical in

def fix {B : Type u} [CommRing B] {ψ : O →+* B} {hB : IsNilpotent (p : B)} (x : P.obj B ψ hB) :
    P.obj B ψ hB :=
  if P.Good x then x else pt B ψ hB

include hpt in
theorem good_fix {B : Type u} [CommRing B] {ψ : O →+* B} {hB : IsNilpotent (p : B)}
    (x : P.obj B ψ hB) : P.Good (P.fix pt x) := by
  unfold fix; split_ifs with h
  · exact h
  · exact hpt _ _ _

theorem fix_of_good {B : Type u} [CommRing B] {ψ : O →+* B} {hB : IsNilpotent (p : B)}
    (x : P.obj B ψ hB) (hx : P.Good x) : P.fix pt x = x := by
  unfold fix; rw [if_pos hx]

def eta (hpt : GoodPt pt) (B : Type u) [CommRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)) (x : P.obj B ψ hB) :
    P.plus.plus.obj B ψ hB :=
  Quotient.mk (Germ.setoid P.plus B ψ hB)
    (Germ.single (P := P.plus) (Quotient.mk (Germ.setoid P B ψ hB)
      (Germ.single (P.fix pt x) (P.good_fix pt hpt x))) trivial)

theorem eta_of_good {B : Type u} [CommRing B] {ψ : O →+* B} {hB : IsNilpotent (p : B)}
    (x : P.obj B ψ hB) (hx : P.Good x) :
    P.eta pt hpt B ψ hB x =
      Quotient.mk (Germ.setoid P.plus B ψ hB)
        (Germ.single (P := P.plus) (Quotient.mk (Germ.setoid P B ψ hB) (Germ.single x hx)) trivial) := by
  unfold eta
  have e : P.fix pt x = x := P.fix_of_good pt x hx
  congr 2
  apply Quotient.sound

  refine Germ.single_agree_of_iso _ _ _ hx ?_
  rw [e]; exact P.iso_refl _ hx

theorem eta_natural {B B' : Type u} [CommRing B] [CommRing B'] {ψ : O →+* B} {ψ' : O →+* B'}
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (φ : B →+* B') (hf : φ.comp ψ = ψ')
    (x : P.obj B ψ hB) (hx : P.Good x) :
    P.eta pt hpt B' ψ' hB' (P.map hB hB' φ hf x) =
      P.plus.plus.map hB hB' φ hf (P.eta pt hpt B ψ hB x) := by
  rw [P.eta_of_good pt hpt _ (P.good_map _ _ _ _ _ hx), P.eta_of_good pt hpt _ hx]
  show _ = Quotient.mk _ ((Germ.single (P := P.plus) _ trivial).map hB' φ hf)
  apply Quotient.sound
  have e : Quotient.mk (Germ.setoid P B' ψ' hB') (Germ.single (P.map hB hB' φ hf x) (P.good_map _ _ _ _ _ hx)) =
      P.plus.map hB hB' φ hf (Quotient.mk (Germ.setoid P B ψ hB) (Germ.single x hx)) := by
    show _ = Quotient.mk _ ((Germ.single x hx).map hB' φ hf)
    exact Quotient.sound (Germ.single_map_agree x hx hB' φ hf).symm
  rw [e]
  exact (Germ.single_map_agree (P := P.plus) _ trivial hB' φ hf).symm

theorem eta_eq_iff {B : Type u} [CommRing B] {ψ : O →+* B} {hB : IsNilpotent (p : B)}
    (hsep : P.SeparatedAt B ψ hB) (x y : P.obj B ψ hB) (hx : P.Good x) (hy : P.Good y) :
    P.eta pt hpt B ψ hB x = P.eta pt hpt B ψ hB y ↔ P.Iso x y := by
  rw [P.eta_of_good pt hpt x hx, P.eta_of_good pt hpt y hy]
  constructor
  · intro h

    obtain ⟨m, g, hg, σ, τ, hσ, hτ, H⟩ := Quotient.exact (s := Germ.setoid P.plus B ψ hB) h
    have A : (Germ.single x hx).Agree (Germ.single y hy) := by
      refine Germ.agree_of_locally P _ _ g hg (fun c => Localization.Away (g c)) (fun c => nilp_loc hB (g c))
        fun c => ?_
      apply Quotient.exact (s := Germ.setoid P _ _ _)
      have := H c
      rw [Germ.single_restr, Germ.single_restr] at this
      exact this
    obtain ⟨m', g', hg', σ', τ', hσ', hτ', H'⟩ := A
    refine hsep x y hx hy m' g' hg' fun c => ?_
    have := H' c
    rwa [Germ.single_restr, Germ.single_restr] at this
  · intro h
    congr 2
    exact Quotient.sound (Germ.single_agree_of_iso x y hx hy h)

theorem eta_locally_surjective {B : Type u} [CommRing B] {ψ : O →+* B} (hB : IsNilpotent (p : B))
    (m : P.plus.plus.obj B ψ hB) :
    ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
      ∀ (i : Fin n) (L : Type u) [CommRing L] [Algebra B L] [IsLocalization.Away (f i) L]
        (hL : IsNilpotent (p : L)),
        ∃ t : P.obj L ((algebraMap B L).comp ψ) hL, P.Good t ∧
          P.eta pt hpt L ((algebraMap B L).comp ψ) hL t =
            P.plus.plus.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m := by
  induction m using Quotient.ind with | _ Γ => ?_

  have hrep : ∀ i, ∃ G : P.Germ (Localization.Away (Γ.f i)) ((algebraMap B _).comp ψ) (nilp_loc hB _),
      Quotient.mk (Germ.setoid P _ _ _) G = Γ.t i := fun i => Quotient.exists_rep (Γ.t i)
  choose G hG using hrep
  refine ⟨∑ i, (G i).n, Refine.H Γ.f (fun i => Localization.Away (Γ.f i)) (fun i => (G i).n) (fun i => (G i).f),
    Refine.span_eq _ _ _ _ Γ.span_eq (fun i => (G i).span_eq), fun k' L _ _ _ hL => ?_⟩
  set i := (finSigmaFinEquiv.symm k').1
  set c := (finSigmaFinEquiv.symm k').2
  have hu : IsUnit (algebraMap B L (Refine.H Γ.f (fun i => Localization.Away (Γ.f i)) (fun i => (G i).n)
      (fun i => (G i).f) k')) := IsLocalization.Away.algebraMap_isUnit _
  have hfi : IsUnit (algebraMap B L (Γ.f i)) := Refine.isUnit_f _ k' hu

  let lam : Localization.Away (Γ.f i) →+* L := IsLocalization.Away.lift (Γ.f i) hfi
  have hlam : lam.comp (algebraMap B _) = algebraMap B L := IsLocalization.Away.lift_comp _ _
  have huc : IsUnit (lam ((G i).f c)) :=
    Refine.isUnit_lam_h (L := fun i => Localization.Away (Γ.f i)) (m := fun i => (G i).n)
      (h := fun i => (G i).f) _ k' hu
  refine ⟨(G i).restr c hL lam (lift_comp_comp _ _ rfl hfi) huc, Germ.good_restr _ _ _ _ _ _, ?_⟩
  rw [P.eta_of_good pt hpt _ (Germ.good_restr _ _ _ _ _ _)]
  show _ = Quotient.mk _ (Γ.map hL (algebraMap B L) rfl)
  apply Quotient.sound

  have u1 : IsUnit (algebraMap L (Localization.Away (1 : L)) (1 : L)) := by
    rw [map_one]; exact isUnit_one
  have ui : IsUnit (algebraMap L (Localization.Away (1 : L)) ((Γ.map hL (algebraMap B L) rfl).f i)) := by
    rw [Germ.map_f]; exact hfi.map _
  have ui' : IsUnit (((algebraMap L (Localization.Away (1 : L))).comp (algebraMap B L)) (Γ.f i)) := by
    rw [RingHom.comp_apply]; exact hfi.map _
  refine ⟨1, fun _ => 1, by simp, fun _ => (0 : Fin 1), fun _ => i, fun _ => u1, fun _ => ui, fun _ => ?_⟩
  set R := Localization.Away (1 : L)
  rw [Germ.single_restr, Germ.restr_map]

  show Quotient.mk _ ((Germ.single _ (Germ.good_restr _ _ _ _ _ _)).map (nilp_loc hL 1) (algebraMap L R) rfl) =
    P.plus.map _ (nilp_loc hL 1) (IsLocalization.Away.lift (Γ.f i) ui') _ (Γ.t i)
  rw [← hG i]
  show _ = Quotient.mk _ ((G i).map (nilp_loc hL 1) (IsLocalization.Away.lift (Γ.f i) ui') _)
  apply Quotient.sound

  have e_lift : (IsLocalization.Away.lift (S := Localization.Away (Γ.f i)) (Γ.f i) ui' : _ →+* R) =
      (algebraMap L R).comp lam := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (Γ.f i))
    rw [IsLocalization.Away.lift_comp, RingHom.comp_assoc, hlam]
  have uc' : IsUnit (algebraMap R (Localization.Away (1 : R))
      (((G i).map (nilp_loc hL 1) (IsLocalization.Away.lift (Γ.f i) ui')
        (lift_comp_comp (Γ.f i) ((algebraMap L R).comp (algebraMap B L)) rfl ui')).f c)) := by
    rw [Germ.map_f, e_lift]
    exact (huc.map (algebraMap L R)).map (algebraMap R (Localization.Away (1 : R)))
  refine ⟨1, fun _ => 1, by simp, fun _ => (0 : Fin 1), fun _ => c,
    fun _ => by
      rw [Germ.map_f]
      show IsUnit (algebraMap R (Localization.Away (1 : R)) (algebraMap L R (1 : L)))
      rw [map_one, map_one]; exact isUnit_one,
    fun _ => uc', fun _ => ?_⟩
  rw [Germ.restr_map, Germ.single_restr, Germ.restr_map, Germ.map_restr]
  exact (G i).restr_iso_of_eq c _ (by rw [e_lift]; rfl) _ _ _ _

end EtaDef

theorem exists_sheafification (pt : P.BasePt) (hpt : GoodPt pt) :
    ∃ (M : ModuliPackage.{u, v} p O) (_ : M.IsZariskiSheaf)
      (η : ∀ (B : Type u) [CommRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)), P.obj B ψ hB → M.obj B ψ hB),
      (∀ (B : Type u) [CommRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)), P.SeparatedAt B ψ hB →
        ∀ (x y : P.obj B ψ hB), P.Good x → P.Good y → (η B ψ hB x = η B ψ hB y ↔ P.Iso x y)) ∧
      (∀ (B B' : Type u) [CommRing B] [CommRing B'] (ψ : O →+* B) (ψ' : O →+* B')
        (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B') (hf : f.comp ψ = ψ')
        (x : P.obj B ψ hB), P.Good x → η B' ψ' hB' (P.map hB hB' f hf x) = M.map hB hB' f hf (η B ψ hB x)) ∧
      (∀ (B : Type u) [CommRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)) (m : M.obj B ψ hB),
        ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
          ∀ (i : Fin n) (L : Type u) [CommRing L] [Algebra B L] [IsLocalization.Away (f i) L]
            (hL : IsNilpotent (p : L)),
            ∃ t : P.obj L ((algebraMap B L).comp ψ) hL, P.Good t ∧
              η L ((algebraMap B L).comp ψ) hL t =
                M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m) :=
  ⟨P.plus.plus.toModuliPackage, P.isZariskiSheaf_plus_plus, P.eta pt hpt,
    fun B _ ψ hB hsep x y hx hy => P.eta_eq_iff pt hpt hsep x y hx hy,
    fun B B' _ _ ψ ψ' hB hB' f hf x hx => P.eta_natural pt hpt hB hB' f hf x hx,
    fun B _ ψ hB m => P.eta_locally_surjective pt hpt hB m⟩

end IsoPkg

end KcR4S211.Sheafify

end

set_option autoImplicit false

noncomputable section

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

namespace KcR4S211
namespace Sheafify

variable {p : ℕ} [Fact p.Prime] {O : Type v} [CommRing O]

section UAdm

variable (ι : Zp2 p →+* O) {Φ : FormalODModule p (O ⧸ pIdeal p O)}

def UAdm {B : Type u} [CommRing B] (ψ : O →+* B) (t : Rigidified p Φ B) : Prop :=
  ∀ (B' : Type u) [CommRing B'] (g : B →+* B'), IsNilpotent (p : B') → (t.map g).IsAdmissible ι (g.comp ψ)

variable {ι}

theorem UAdm.isAdmissible {B : Type u} [CommRing B] {ψ : O →+* B} {t : Rigidified p Φ B}
    (hB : IsNilpotent (p : B)) (h : UAdm ι ψ t) : t.IsAdmissible ι ψ := by
  have h' := h B (RingHom.id B) hB
  rwa [Rigidified.map_id, RingHom.id_comp] at h'

theorem UAdm.of_isAdmissible {B : Type u} [CommRing B] [IsNoetherianRing B] {ψ : O →+* B}
    {t : Rigidified p Φ B} (h : t.IsAdmissible ι ψ) : UAdm ι ψ t :=
  fun B' _ g _ => Rigidified.IsAdmissible.map_ringHom ι ψ g t h

theorem UAdm.map {B B' : Type u} [CommRing B] [CommRing B'] {ψ : O →+* B} {ψ' : O →+* B'}
    {t : Rigidified p Φ B} (g : B →+* B') (hg : g.comp ψ = ψ') (h : UAdm ι ψ t) :
    UAdm ι ψ' (t.map g) := by
  intro B'' _ g' hB''
  rw [← Rigidified.map_comp, ← hg, ← RingHom.comp_assoc]
  exact h B'' (g'.comp g) hB''

theorem UAdm.constantCoeff_ρ {B : Type u} [CommRing B] {ψ : O →+* B} {t : Rigidified p Φ B}
    (hB : IsNilpotent (p : B)) (h : UAdm ι ψ t) (i : Fin 2) : constantCoeff (t.ρ i) = 0 :=
  (UAdm.isAdmissible hB h).constantCoeff_ρ i

end UAdm

def rigidPkg (ι : Zp2 p →+* O) (Φ : FormalODModule p (O ⧸ pIdeal p O)) : IsoPkg.{u, v} p O where
  obj B _ ψ hB := Rigidified p Φ B
  map hB hB' f hf t := t.map f
  map_id hB x := Rigidified.map_id x
  map_comp hB hB' hB'' g f hf hg x := Rigidified.map_comp g f x
  Iso := fun {B} _ {ψ} {hB} t t' => t.IsIsomorphic t'
  Good := fun {B} _ {ψ} {hB} t => UAdm ι ψ t
  good_map hB hB' f hf x hx := UAdm.map f hf hx
  iso_map hB hB' f hf x y hx hy hxy :=
    Rigidified.IsIsomorphic.map_ringHom f x y (UAdm.constantCoeff_ρ hB hx) (UAdm.constantCoeff_ρ hB hy) hxy
  iso_refl := fun {B} _ {ψ} {hB} x hx => Rigidified.IsIsomorphic.refl x (UAdm.constantCoeff_ρ hB hx)
  iso_symm := fun {B} _ {ψ} {hB} x y hx hy hxy =>
    Rigidified.IsIsomorphic.symm hxy (UAdm.constantCoeff_ρ hB hx) (UAdm.constantCoeff_ρ hB hy)
  iso_trans := fun {B} _ {ψ} {hB} x y _ hx hy hz hxy hyz =>
    Rigidified.IsIsomorphic.trans hxy hyz (UAdm.constantCoeff_ρ hB hx) (UAdm.constantCoeff_ρ hB hy)
      (UAdm.constantCoeff_ρ hB hz)

section simp_lemmas

variable (ι : Zp2 p →+* O) (Φ : FormalODModule p (O ⧸ pIdeal p O))

@[scoped simp] theorem rigidPkg_obj (B : Type u) [CommRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)) :
    (rigidPkg ι Φ).obj B ψ hB = Rigidified p Φ B := rfl

@[scoped simp] theorem rigidPkg_map {B B' : Type u} [CommRing B] [CommRing B'] {ψ : O →+* B} {ψ' : O →+* B'}
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B') (hf : f.comp ψ = ψ')
    (t : Rigidified p Φ B) :
    (rigidPkg ι Φ).map hB hB' f hf t = t.map f := rfl

@[scoped simp] theorem rigidPkg_Iso {B : Type u} [CommRing B] {ψ : O →+* B} {hB : IsNilpotent (p : B)}
    (t t' : Rigidified p Φ B) :
    (rigidPkg ι Φ).Iso (ψ := ψ) (hB := hB) t t' = t.IsIsomorphic t' := rfl

@[scoped simp] theorem rigidPkg_Good {B : Type u} [CommRing B] {ψ : O →+* B} {hB : IsNilpotent (p : B)}
    (t : Rigidified p Φ B) :
    (rigidPkg ι Φ).Good (ψ := ψ) (hB := hB) t = UAdm ι ψ t := rfl

end simp_lemmas

theorem rigidPkg_separatedAt (ι : Zp2 p →+* O) (Φ : FormalODModule p (O ⧸ pIdeal p O))
    {B : Type u} [CommRing B] [IsNoetherianRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)) :
    (rigidPkg ι Φ).SeparatedAt B ψ hB := by
  intro x y hx hy n f hf hloc
  exact Rigidified.isIsomorphic_of_forall_isIsomorphic_map_localizationAway ι ψ hB x y
    (UAdm.isAdmissible hB hx) (UAdm.isAdmissible hB hy) n f hf hloc

section BasePoint

variable (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
  (ι : Zp2 p →+* WittVector p k)
  (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))

omit [Fact p.Prime] in
theorem residueMap_mk' {O' : Type*} [CommRing O'] {B : Type*} [CommRing B] (ψ : O' →+* B) (x : O') :
    residueMap (p := p) ψ (Ideal.Quotient.mk (pIdeal p O') x) = Ideal.Quotient.mk (pIdeal p B) (ψ x) := rfl

variable (p) in

def X0 : FormalODModule p (Zp2 p) :=
  (CerednikDrinfeld.FormalODModule.exists_forall_isSpecial_map_and_hasHeight_four_map_of_isNilpotent.{0} p).choose

theorem X0_spec (B : Type) [CommRing B] (j : Zp2 p →+* B) (hB : IsNilpotent (p : B)) :
    ((X0 p).map j).IsSpecial j ∧ ((X0 p).map j).HasHeight 4 :=
  (CerednikDrinfeld.FormalODModule.exists_forall_isSpecial_map_and_hasHeight_four_map_of_isNilpotent.{0}
    p).choose_spec B j hB

theorem isNilpotent_natCast_field : IsNilpotent (p : k) := by
  rw [CharP.cast_eq_zero]
  exact IsNilpotent.zero

theorem exists_fieldTriple (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
    (hΦ4 : Φ.HasHeight 4) :
    ∃ t : Rigidified p Φ k,
      t.X = (X0 p).map ((WittVector.constantCoeff : WittVector p k →+* k).comp ι) ∧
        t.IsAdmissible ι (WittVector.constantCoeff : WittVector p k →+* k) := by
  set cc : WittVector p k →+* k := WittVector.constantCoeff
  obtain ⟨hXk, hXk4⟩ := X0_spec k (cc.comp ι) (isNilpotent_natCast_field k)
  let Xk : SpecialFormalODModule p (structureMap ι cc) :=
    { toFormalODModule := (X0 p).map (cc.comp ι), isSpecial := hXk, hasHeight := hXk4 }
  have hΦ' : (Φ.map (residueMap cc)).IsSpecial
      ((residueMap cc).comp ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι)) :=
    CerednikDrinfeld.FormalODModule.IsSpecial.map _ (residueMap cc) Φ hΦ
  have hΦ4' : (Φ.map (residueMap cc)).HasHeight 4 := by
    show FormalODModule.HasKernelOfDegree ((Φ.act (p : Zp2 p)).map (residueMap cc)) (p ^ 4)
    exact CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map (residueMap cc) _ (Φ.isLawHom_act _).1 hΦ4
  obtain ⟨t₀, ht₀X, ht₀⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.exists_X_eq_and_isAdmissible_of_isAlgClosed p ι Φ k cc hΦ' hΦ4' Xk
  exact ⟨t₀, ht₀X, ht₀⟩

def T0 (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι)) (hΦ4 : Φ.HasHeight 4) :
    Rigidified p Φ k :=
  (exists_fieldTriple k ι Φ hΦ hΦ4).choose

theorem T0_spec (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι)) (hΦ4 : Φ.HasHeight 4) :
    (T0 k ι Φ hΦ hΦ4).X = (X0 p).map ((WittVector.constantCoeff : WittVector p k →+* k).comp ι) ∧
      (T0 k ι Φ hΦ hΦ4).IsAdmissible ι (WittVector.constantCoeff : WittVector p k →+* k) :=
  (exists_fieldTriple k ι Φ hΦ hΦ4).choose_spec

def hmap {B : Type} [CommRing B] (ψ : WittVector p k →+* B) : k ⧸ pIdeal p k →+* B ⧸ pIdeal p B :=
  Ideal.Quotient.lift (pIdeal p k)
    ((residueMap ψ).comp
      (WittVector.quotientPEquiv : WittVector p k ⧸ pIdeal p (WittVector p k) ≃+* k).symm.toRingHom)
    (by
      intro a ha
      have hbot : pIdeal p k = ⊥ := by
        rw [pIdeal, Ideal.span_singleton_eq_bot, CharP.cast_eq_zero]
      rw [hbot, Ideal.mem_bot] at ha
      rw [ha, map_zero])

theorem hmap_mk {B : Type} [CommRing B] (ψ : WittVector p k →+* B) (x : WittVector p k) :
    hmap k ψ (Ideal.Quotient.mk (pIdeal p k) (WittVector.constantCoeff x)) = Ideal.Quotient.mk (pIdeal p B) (ψ x) := by
  set e : WittVector p k ⧸ pIdeal p (WittVector p k) ≃+* k := WittVector.quotientPEquiv
  have he : e (Ideal.Quotient.mk (pIdeal p (WittVector p k)) x) = WittVector.constantCoeff x := rfl
  have hes : e.symm (WittVector.constantCoeff x) = Ideal.Quotient.mk (pIdeal p (WittVector p k)) x := by
    rw [← he, RingEquiv.symm_apply_apply]
  show ((residueMap ψ).comp e.symm.toRingHom) (WittVector.constantCoeff x) = _
  show residueMap ψ (e.symm (WittVector.constantCoeff x)) = _
  rw [hes]
  rfl

theorem hmap_comp_residueMap {B : Type} [CommRing B] (ψ : WittVector p k →+* B) :
    (hmap k ψ).comp (residueMap (WittVector.constantCoeff : WittVector p k →+* k)) = residueMap ψ := by
  apply Ideal.Quotient.ringHom_ext
  ext x
  show hmap k ψ (residueMap _ (Ideal.Quotient.mk _ x)) = residueMap ψ (Ideal.Quotient.mk _ x)
  rw [residueMap_mk', residueMap_mk', hmap_mk]

theorem reduceMap_comp_hmap {B B' : Type} [CommRing B] [CommRing B'] (ψ : WittVector p k →+* B) (g : B →+* B') :
    (reduceMap g).comp (hmap k ψ) = hmap k (g.comp ψ) := by
  apply Ideal.Quotient.ringHom_ext
  ext c
  obtain ⟨x, rfl⟩ := WittVector.constantCoeff_surjective (p := p) c
  show reduceMap g (hmap k ψ (Ideal.Quotient.mk _ (WittVector.constantCoeff x))) =
    hmap k (g.comp ψ) (Ideal.Quotient.mk _ (WittVector.constantCoeff x))
  rw [hmap_mk, hmap_mk]
  rfl

def bpt (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι)) (hΦ4 : Φ.HasHeight 4)
    {B : Type} [CommRing B] (ψ : WittVector p k →+* B) : Rigidified p Φ B :=
  ⟨(X0 p).map (ψ.comp ι), (T0 k ι Φ hΦ hΦ4).n, (T0 k ι Φ hΦ hΦ4).ρ.map (hmap k ψ)⟩

theorem bpt_map (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι)) (hΦ4 : Φ.HasHeight 4)
    {B B' : Type} [CommRing B] [CommRing B'] (ψ : WittVector p k →+* B) (g : B →+* B') :
    (bpt k ι Φ hΦ hΦ4 ψ).map g = bpt k ι Φ hΦ hΦ4 (g.comp ψ) := by
  refine Rigidified.ext' ?_ rfl ?_
  · show ((X0 p).map (ψ.comp ι)).map g = (X0 p).map ((g.comp ψ).comp ι)
    rw [FormalODModule.map_map]
    rfl
  · show ((T0 k ι Φ hΦ hΦ4).ρ.map (hmap k ψ)).map (reduceMap g) = (T0 k ι Φ hΦ hΦ4).ρ.map (hmap k (g.comp ψ))
    rw [Series.map_map, reduceMap_comp_hmap]

theorem bpt_isAdmissible (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
    (hΦ4 : Φ.HasHeight 4) {B : Type} [CommRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)) :
    (bpt k ι Φ hΦ hΦ4 ψ).IsAdmissible ι ψ := by
  set cc : WittVector p k →+* k := WittVector.constantCoeff
  obtain ⟨hXB, hXB4⟩ := X0_spec (p := p) B (ψ.comp ι) hB
  obtain ⟨ht₀X, -, -, hiso⟩ := T0_spec k ι Φ hΦ hΦ4
  have hcomp' : ((hmap k ψ).comp (Ideal.Quotient.mk (pIdeal p k))).comp (cc.comp ι) =
      (Ideal.Quotient.mk (pIdeal p B)).comp (ψ.comp ι) := by
    ext x
    exact hmap_mk k ψ (ι x)
  refine ⟨hXB, hXB4, ?_, ?_⟩
  · have H := hiso.1.map (hmap k ψ)
    have e1 : ((T0 k ι Φ hΦ hΦ4).Φbar cc).map (hmap k ψ) = Φ.map (residueMap ψ) := by
      show (Φ.map (residueMap cc)).map (hmap k ψ) = Φ.map (residueMap ψ)
      rw [FormalODModule.map_map, hmap_comp_residueMap]
    have e2 : (T0 k ι Φ hΦ hΦ4).Xbar.map (hmap k ψ) =
        ((X0 p).map (ψ.comp ι)).map (Ideal.Quotient.mk (pIdeal p B)) := by
      show ((T0 k ι Φ hΦ hΦ4).X.map (Ideal.Quotient.mk (pIdeal p k))).map (hmap k ψ) = _
      rw [ht₀X]
      show (((X0 p).map (cc.comp ι)).map (Ideal.Quotient.mk (pIdeal p k))).map (hmap k ψ) = _
      rw [FormalODModule.map_map, FormalODModule.map_map, FormalODModule.map_map, hcomp']
    rw [e1, e2] at H
    exact H
  · exact CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map (hmap k ψ) (T0 k ι Φ hΦ hΦ4).ρ
      (fun i => hiso.1.constantCoeff i) hiso.2

def basePt (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι)) (hΦ4 : Φ.HasHeight 4) :
    (rigidPkg.{0, 0} ι Φ).BasePt :=
  fun B _ ψ _ => bpt k ι Φ hΦ hΦ4 ψ

theorem goodPt_basePt (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
    (hΦ4 : Φ.HasHeight 4) : IsoPkg.GoodPt (basePt k ι Φ hΦ hΦ4) := by
  intro B _ ψ _ B' _ g hB'
  show ((bpt k ι Φ hΦ hΦ4 ψ).map g).IsAdmissible ι (g.comp ψ)
  rw [bpt_map]
  exact bpt_isAdmissible k ι Φ hΦ hΦ4 (g.comp ψ) hB'

end BasePoint

end KcR4S211.Sheafify
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_moduliPackage_isZariskiSheaf_eta_iff_isIsomorphic_and_natural_and_cover.KcR4S211 P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_moduliPackage_isZariskiSheaf_eta_iff_isIsomorphic_and_natural_and_cover.KcR4S211.Sheafify"
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_moduliPackage_isZariskiSheaf_eta_iff_isIsomorphic_and_natural_and_cover.KcR4S211"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_moduliPackage_isZariskiSheaf_eta_iff_isIsomorphic_and_natural_and_cover.KcR4S211 P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_moduliPackage_isZariskiSheaf_eta_iff_isIsomorphic_and_natural_and_cover.KcR4S211.Sheafify"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal KcR4S211.Sheafify

theorem solution
(p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
(ι : Zp2 p →+* WittVector p k)
(Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
(hΦ4 : Φ.HasHeight 4)
    :
    ∃ (M : ModuliPackage.{0, 0} p (WittVector p k)) (_ : M.IsZariskiSheaf)
      (η : ∀ (B : Type) [CommRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)),
Rigidified p Φ B → M.obj B ψ hB),
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
(t t' : Rigidified p Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
(η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
(∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : WittVector p k →+* B) (ψ' : WittVector p k →+* B')
(hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B')
(hf : f.comp ψ = ψ') (t : Rigidified p Φ B), t.IsAdmissible ι ψ →
η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t)) ∧
(∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)) (m : M.obj B ψ hB),
∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
(hL : IsNilpotent (p : L)),
∃ t : Rigidified p Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
η L ((algebraMap B L).comp ψ) hL t =
M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m) := by
  obtain ⟨M, hM, η, h1, h2, h3⟩ := (rigidPkg ι Φ).exists_sheafification (basePt k ι Φ hΦ hΦ4)
    (goodPt_basePt k ι Φ hΦ hΦ4)
  refine ⟨M, hM, η, ?_, ?_, ?_⟩
  · intro B _ _ ψ hB t t' ht ht'
    exact h1 B ψ hB (rigidPkg_separatedAt ι Φ ψ hB) t t' (UAdm.of_isAdmissible ht)
      (UAdm.of_isAdmissible ht')
  · intro B B' _ _ _ _ ψ ψ' hB hB' f hf t ht
    exact h2 B B' ψ ψ' hB hB' f hf t (UAdm.of_isAdmissible ht)
  · intro B _ _ ψ hB m
    obtain ⟨n, f, hf, H⟩ := h3 B ψ hB m
    refine ⟨n, f, hf, fun i L _ _ _ _ hL => ?_⟩
    obtain ⟨t, ht, e⟩ := H i L hL
    exact ⟨t, UAdm.isAdmissible hL ht, e⟩

end S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_moduliPackage_isZariskiSheaf_eta_iff_isIsomorphic_and_natural_and_cover
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_moduliPackage_isZariskiSheaf_eta_iff_isIsomorphic_and_natural_and_cover (solution)
