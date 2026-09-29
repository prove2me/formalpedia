-- Prove2me | solution 1 for CommRingCat.isPushout_of_isPullback_of_isPullback_of_isPushout_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/9f366c6b-dca3-58e2-9975-980c80bf3c3a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CommRingCat_isPushout_of_isPullback_of_isPullback_of_isPushout_of_surjective

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u

namespace RBCProof

theorem pb_exists {P X Y Z : CommRingCat.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) (x : X) (y : Y) (hxy : f x = g y) : ∃ p : P, fst p = x ∧ snd p = y := by
  let e := h.isLimit.conePointUniqueUpToIso (CommRingCat.pullbackConeIsLimit f g)
  have h1 := h.isLimit.conePointUniqueUpToIso_inv_comp (CommRingCat.pullbackConeIsLimit f g) WalkingCospan.left
  have h2 := h.isLimit.conePointUniqueUpToIso_inv_comp (CommRingCat.pullbackConeIsLimit f g) WalkingCospan.right
  let v : RingHom.eqLocus (f.hom.comp (RingHom.fst X Y)) (g.hom.comp (RingHom.snd X Y)) := ⟨(x, y), hxy⟩
  refine ⟨e.inv v, ?_, ?_⟩
  · have := congrArg (fun k : _ ⟶ X => k v) h1
    simp [CommRingCat.pullbackCone] at this
    exact this
  · have := congrArg (fun k : _ ⟶ Y => k v) h2
    simp [CommRingCat.pullbackCone] at this
    exact this

theorem pb_ext {P X Y Z : CommRingCat.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) (p q : P) (h1 : fst p = fst q) (h2 : snd p = snd q) : p = q := by
  let e := h.isLimit.conePointUniqueUpToIso (CommRingCat.pullbackConeIsLimit f g)
  have k1 := h.isLimit.conePointUniqueUpToIso_hom_comp (CommRingCat.pullbackConeIsLimit f g) WalkingCospan.left
  have k2 := h.isLimit.conePointUniqueUpToIso_hom_comp (CommRingCat.pullbackConeIsLimit f g) WalkingCospan.right
  have hinj : Function.Injective e.hom := e.commRingCatIsoToRingEquiv.injective
  apply hinj
  have k1p := congrArg (fun k : P ⟶ X => k p) k1
  have k1q := congrArg (fun k : P ⟶ X => k q) k1
  have k2p := congrArg (fun k : P ⟶ Y => k p) k2
  have k2q := congrArg (fun k : P ⟶ Y => k q) k2
  simp only [CommRingCat.pullbackCone, PullbackCone.mk_π_app_left, PullbackCone.mk_π_app_right, CommRingCat.hom_comp,
    CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply] at k1p k1q k2p k2q
  apply Subtype.ext
  apply Prod.ext
  · exact k1p.trans (h1.trans k1q.symm)
  · exact k2p.trans (h2.trans k2q.symm)

theorem po_surj {C C₀ A A₀ : CommRingCat.{u}} {φ : C ⟶ C₀} {u : C ⟶ A} {u₀ : C₀ ⟶ A₀} {q : A ⟶ A₀}
    (h : IsPushout φ u u₀ q) (hφ : Function.Surjective φ) : Function.Surjective q := by
  have htop := CommRingCat.closure_range_union_range_eq_top_of_isPushout h
  have hsub : Set.range u₀ ∪ Set.range q ⊆ (q.hom.range : Set A₀) := by
    rintro z (⟨c₀, rfl⟩ | ⟨a, rfl⟩)
    · obtain ⟨c, rfl⟩ := hφ c₀
      refine ⟨u c, ?_⟩
      have := congrArg (fun k : C ⟶ A₀ => k c) h.w
      simpa using this.symm
    · exact ⟨a, rfl⟩
  have hle : Subring.closure (Set.range u₀ ∪ Set.range q) ≤ q.hom.range := Subring.closure_le.mpr hsub
  rw [htop, top_le_iff] at hle
  intro z
  have hz : z ∈ q.hom.range := hle ▸ Subring.mem_top z
  exact hz

theorem po_ker {C C₀ A A₀ : CommRingCat.{u}} {φ : C ⟶ C₀} {u : C ⟶ A} {u₀ : C₀ ⟶ A₀} {q : A ⟶ A₀}
    (h : IsPushout φ u u₀ q) (hφ : Function.Surjective φ) :
    RingHom.ker q.hom = (RingHom.ker φ.hom).map u.hom := by
  apply le_antisymm
  ·
    set I : Ideal A := (RingHom.ker φ.hom).map u.hom with hI
    have hker : RingHom.ker φ.hom ≤ RingHom.ker ((Ideal.Quotient.mk I).comp u.hom) := by
      intro c hc
      rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ hc
    let c₀ : C₀ →+* A ⧸ I := φ.hom.liftOfSurjective hφ ⟨(Ideal.Quotient.mk I).comp u.hom, hker⟩
    have hc₀ : c₀.comp φ.hom = (Ideal.Quotient.mk I).comp u.hom := RingHom.liftOfSurjective_comp _ hφ _
    have hw : φ ≫ CommRingCat.ofHom c₀ = u ≫ CommRingCat.ofHom (Ideal.Quotient.mk I) := by
      ext c
      exact congrArg (fun k : C →+* A ⧸ I => k c) hc₀
    let d := h.desc (CommRingCat.ofHom c₀) (CommRingCat.ofHom (Ideal.Quotient.mk I)) hw
    have hd : q ≫ d = CommRingCat.ofHom (Ideal.Quotient.mk I) := h.inr_desc _ _ hw
    intro x hx
    rw [RingHom.mem_ker] at hx
    have := congrArg (fun k : A ⟶ CommRingCat.of (A ⧸ I) => k x) hd
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, hx, map_zero, CommRingCat.hom_ofHom] at this
    exact Ideal.Quotient.eq_zero_iff_mem.mp this.symm
  · rw [Ideal.map_le_iff_le_comap]
    intro c hc
    rw [RingHom.mem_ker] at hc
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have := congrArg (fun k : C ⟶ A₀ => k c) h.w
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, hc, map_zero] at this
    exact this.symm

theorem half {P C' C'' C₀ A A' A'' A₀ : CommRingCat.{u}}
    {p' : P ⟶ C'} {p'' : P ⟶ C''} {φ' : C' ⟶ C₀} {φ'' : C'' ⟶ C₀} (hC : IsPullback p' p'' φ' φ'')
    {a' : A ⟶ A'} {a'' : A ⟶ A''} {q' : A' ⟶ A₀} {q'' : A'' ⟶ A₀} (hA : IsPullback a' a'' q' q'')
    (u : P ⟶ A) (u' : C' ⟶ A') (u'' : C'' ⟶ A'') (u₀ : C₀ ⟶ A₀)
    (hu' : p' ≫ u' = u ≫ a') (hu'' : p'' ≫ u'' = u ≫ a'') (hq' : φ' ≫ u₀ = u' ≫ q') (hq'' : φ'' ≫ u₀ = u'' ≫ q'')
    (hφ' : Function.Surjective φ'.hom) (hφ'' : Function.Surjective φ''.hom)
    (hco' : IsPushout φ' u' u₀ q') (hco'' : IsPushout φ'' u'' u₀ q'') :
    IsPushout p' u u' a' := by

  have hq''s : Function.Surjective q''.hom := po_surj hco'' hφ''
  have hq's : Function.Surjective q'.hom := po_surj hco' hφ'
  have hp's : Function.Surjective p'.hom := by
    intro c'
    obtain ⟨c'', hc''⟩ := hφ'' (φ' c')
    obtain ⟨j, hj, -⟩ := pb_exists hC c' c'' hc''.symm
    exact ⟨j, hj⟩
  have ha's : Function.Surjective a'.hom := by
    intro x'
    obtain ⟨x'', hx''⟩ := hq''s (q' x')
    obtain ⟨x, hx, -⟩ := pb_exists hA x' x'' hx''.symm
    exact ⟨x, hx⟩
  have ha''s : Function.Surjective a''.hom := by
    intro x''
    obtain ⟨x', hx'⟩ := hq's (q'' x'')
    obtain ⟨x, -, hx⟩ := pb_exists hA x' x'' hx'
    exact ⟨x, hx⟩

  have hker : RingHom.ker a'.hom ≤ (RingHom.ker p'.hom).map u.hom := by

    have key : ∀ x'' ∈ (RingHom.ker φ''.hom).map u''.hom, ∃ z ∈ (RingHom.ker p'.hom).map u.hom, a' z = 0 ∧ a'' z = x'' := by
      intro x'' hx''
      refine Submodule.span_induction (p := fun x'' _ => ∃ z ∈ (RingHom.ker p'.hom).map u.hom, a' z = 0 ∧ a'' z = x'') ?_ ?_ ?_ ?_ hx''
      · rintro y ⟨i, hi, rfl⟩
        obtain ⟨j, hj1, hj2⟩ := pb_exists hC (0 : C') i (by rw [map_zero]; exact (RingHom.mem_ker.mp hi).symm)
        refine ⟨u j, Ideal.mem_map_of_mem _ (by rw [RingHom.mem_ker]; exact hj1), ?_, ?_⟩
        · have := congrArg (fun k : P ⟶ A' => k j) hu'
          simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, hj1, map_zero] at this
          exact this.symm
        · have := congrArg (fun k : P ⟶ A'' => k j) hu''
          simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, hj2] at this
          exact this.symm
      · exact ⟨0, Ideal.zero_mem _, map_zero _, map_zero _⟩
      · rintro x y - - ⟨z, hz, hz1, hz2⟩ ⟨w, hw, hw1, hw2⟩
        exact ⟨z + w, Ideal.add_mem _ hz hw, by rw [map_add, hz1, hw1, add_zero], by rw [map_add, hz2, hw2]⟩
      · rintro r x - ⟨z, hz, hz1, hz2⟩
        obtain ⟨s, rfl⟩ := ha''s r
        exact ⟨s * z, Ideal.mul_mem_left _ _ hz, by rw [map_mul, hz1, mul_zero], by rw [smul_eq_mul, map_mul, hz2]⟩
    intro x hx
    rw [RingHom.mem_ker] at hx
    have hx'' : a'' x ∈ (RingHom.ker φ''.hom).map u''.hom := by
      rw [← po_ker hco'' hφ'', RingHom.mem_ker]
      have := congrArg (fun k : A ⟶ A₀ => k x) hA.w
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, hx, map_zero] at this
      exact this.symm
    obtain ⟨z, hz, hz1, hz2⟩ := key _ hx''
    have : x = z := pb_ext hA x z (by rw [hx, hz1]) (by rw [hz2])
    rw [this]; exact hz

  refine IsPushout.of_isColimit' ⟨hu'⟩ (PushoutCocone.IsColimit.mk hu' (fun s => CommRingCat.ofHom
      (a'.hom.liftOfSurjective ha's ⟨s.inr.hom, hker.trans ?_⟩)) ?_ ?_ ?_)
  ·
    rw [Ideal.map_le_iff_le_comap]
    intro j hj
    rw [RingHom.mem_ker] at hj
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have := congrArg (fun k : P ⟶ s.pt => k j) s.condition
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, hj, map_zero] at this
    exact this.symm
  · intro s
    ext c'
    obtain ⟨j, rfl⟩ := hp's c'
    have h1 := congrArg (fun k : P ⟶ A' => k j) hu'
    have h2 := congrArg (fun k : P ⟶ s.pt => k j) s.condition
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h1 h2
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom, h1,
      RingHom.liftOfSurjective_comp_apply]
    exact h2.symm
  · intro s
    ext x
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom,
      RingHom.liftOfSurjective_comp_apply]
  · intro s m h1 h2
    ext x'
    obtain ⟨x, rfl⟩ := ha's x'
    have := congrArg (fun k : A ⟶ s.pt => k x) h2
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at this
    simp only [CommRingCat.hom_ofHom, RingHom.liftOfSurjective_comp_apply, this]

end RBCProof

theorem solution
    {P C' C'' C₀ A A' A'' A₀ : CommRingCat.{u}}
    {p' : P ⟶ C'} {p'' : P ⟶ C''} {φ' : C' ⟶ C₀} {φ'' : C'' ⟶ C₀} (hC : IsPullback p' p'' φ' φ'')
    {a' : A ⟶ A'} {a'' : A ⟶ A''} {q' : A' ⟶ A₀} {q'' : A'' ⟶ A₀} (hA : IsPullback a' a'' q' q'')
    (u : P ⟶ A) (u' : C' ⟶ A') (u'' : C'' ⟶ A'') (u₀ : C₀ ⟶ A₀)
    (hu' : p' ≫ u' = u ≫ a') (hu'' : p'' ≫ u'' = u ≫ a'') (hq' : φ' ≫ u₀ = u' ≫ q') (hq'' : φ'' ≫ u₀ = u'' ≫ q'')
    (hφ' : Function.Surjective φ'.hom) (hφ'' : Function.Surjective φ''.hom)
    (hco' : IsPushout φ' u' u₀ q') (hco'' : IsPushout φ'' u'' u₀ q'') :
    IsPushout p' u u' a' ∧ IsPushout p'' u u'' a'' :=
  ⟨RBCProof.half hC hA u u' u'' u₀ hu' hu'' hq' hq'' hφ' hφ'' hco' hco'',
   RBCProof.half hC.flip hA.flip u u'' u' u₀ hu'' hu' hq'' hq' hφ'' hφ' hco'' hco'⟩

end S_CommRingCat_isPushout_of_isPullback_of_isPullback_of_isPushout_of_surjective
end P2MW
export P2MW.S_CommRingCat_isPushout_of_isPullback_of_isPullback_of_isPushout_of_surjective (solution)
