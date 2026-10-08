-- Prove2me | solution 1 for Garban.isAmenable_IET_of_forall_isExtensivelyAmenable_wobbling
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T13:29:04.109925+00:00
-- url     : https://prove2.me/submissions/fd645066-2d01-43af-9935-7e490a198aee

import Mathlib
import Definitions.Def_IntervalExchange
import Theorems.Thm_JMMS_isAmenable_iff_isExtensivelyAmenable_of_le_IET
import Theorems.Thm_JMMS_isExtensivelyAmenable_tfae

section

open IntervalExchange

namespace Garban


namespace IETG
/-- A finitely generated abelian group embeds injectively in some `ℤ^d` with bounded jumps
along each fixed translation (via `A ≅ ℤⁿ × T`, `T` finite). -/
lemma exists_embedding {A : Type*} [AddCommGroup A] [AddGroup.FG A] :
    ∃ (d : ℕ) (ψ : A → Fin d → ℤ), Function.Injective ψ ∧
      ∀ s : A, ∃ L : ℕ, ∀ a : A, ∀ i, |ψ (a + s) i - ψ a i| ≤ L := by
  obtain ⟨n, ι, _, p, hp, e, ⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod A
  have : ∀ i, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  set T := DirectSum ι fun i => ZMod (p i ^ e i)
  have : Finite T := Finite.of_injective (fun x : T => (fun i => x i)) DFunLike.coe_injective
  let N : ℕ := Nat.card T
  let ιT : T → ℤ := fun t => ((Finite.equivFin T t : Fin N) : ℕ)
  have hι0 : ∀ t, 0 ≤ ιT t := fun t => Int.natCast_nonneg _
  have hι1 : ∀ t, ιT t < N := fun t => by
    simp only [ιT]; exact_mod_cast (Finite.equivFin T t).isLt
  have hιinj : Function.Injective ιT := by
    intro a b h
    simp only [ιT, Nat.cast_inj] at h
    exact (Finite.equivFin T).injective (Fin.ext h)
  let ψ : A → Fin (n + 1) → ℤ := fun a => Fin.cons (ιT (f a).2) (fun j => (f a).1 j)
  refine ⟨n + 1, ψ, ?_, fun s => ?_⟩
  · intro a b h
    have h0 := congrFun h 0
    simp only [ψ, Fin.cons_zero] at h0
    apply f.injective
    refine Prod.ext ?_ (hιinj h0)
    ext j
    have := congrFun h j.succ
    simpa [ψ] using this
  · refine ⟨N + ∑ j, ((f s).1 j).natAbs, fun a i => ?_⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [ψ, Fin.cons_zero, map_add, Prod.snd_add]
      have := hι0 ((f a).2 + (f s).2); have := hι1 ((f a).2 + (f s).2)
      have := hι0 (f a).2; have := hι1 (f a).2
      have : |ιT ((f a).2 + (f s).2) - ιT (f a).2| ≤ N := abs_le.mpr ⟨by linarith, by linarith⟩
      have h2 : (0 : ℤ) ≤ ((∑ j, ((f s).1 j).natAbs : ℕ) : ℤ) := Int.natCast_nonneg _
      push_cast at h2 ⊢
      linarith
    · simp only [ψ, Fin.cons_succ, map_add, Prod.fst_add, Finsupp.coe_add, Pi.add_apply,
        add_sub_cancel_left]
      have h1 : ((f s).1 j).natAbs ≤ ∑ j, ((f s).1 j).natAbs :=
        Finset.single_le_sum (f := fun j => ((f s).1 j).natAbs) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ j)
      rw [Int.abs_eq_natAbs]
      push_cast
      have : (((f s).1 j).natAbs : ℤ) ≤ ((∑ j, ((f s).1 j).natAbs : ℕ) : ℤ) := by exact_mod_cast h1
      push_cast at this
      linarith [Int.natCast_nonneg N]

/-- Every element of `IET` has finitely many angles. -/
theorem angles_finite_of_mem_IET {g : Equiv.Perm UnitAddCircle} (hg : g ∈ IET) :
    (angles g).Finite := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx.2.1
  | one => exact (Set.finite_singleton 0).subset (by rintro _ ⟨x, rfl⟩; simp)
  | mul g h _ _ hg hh =>
    refine (hg.add hh).subset ?_
    rintro _ ⟨x, rfl⟩
    refine ⟨g (h x) - h x, ⟨h x, rfl⟩, h x - x, ⟨x, rfl⟩, ?_⟩
    simp [Equiv.Perm.mul_apply]
  | inv g _ hg =>
    refine hg.neg.subset ?_
    rintro _ ⟨x, rfl⟩
    rw [Set.mem_neg]
    exact ⟨g⁻¹ x, by simp⟩

/-- Part (a), integer form: an injective map of each orbit into `ℤ^d` whose coordinates move by
at most `L` along each generator. -/
theorem exists_embedding_orbit (G : Subgroup (Equiv.Perm UnitAddCircle)) (hG : G ≤ IET)
    (S : Finset (Equiv.Perm UnitAddCircle)) (hS : ∀ s ∈ S, s ∈ G)
    (hcl : Subgroup.closure (S : Set (Equiv.Perm UnitAddCircle)) = G) (x : UnitAddCircle) :
    ∃ (d : ℕ) (f : UnitAddCircle → (Fin d → ℤ)) (L : ℕ),
      Set.InjOn f (MulAction.orbit G x) ∧
        ∀ y ∈ MulAction.orbit G x, ∀ s ∈ S, ∀ i, |f (s y) i - f y i| ≤ L := by
  classical
  set Λ : AddSubgroup UnitAddCircle := AddSubgroup.closure (⋃ s ∈ S, angles s) with hΛ
  have hang : ∀ s ∈ S, ∀ z, s z - z ∈ Λ := fun s hs z =>
    AddSubgroup.subset_closure (Set.mem_biUnion hs ⟨z, rfl⟩)
  have hΛfg : Λ.FG := by
    refine ⟨(S.finite_toSet.biUnion fun g hg => angles_finite_of_mem_IET (hG (hS g hg))).toFinset,
      ?_⟩
    simp [hΛ]
  have : AddGroup.FG Λ := (AddGroup.fg_iff_addSubgroup_fg Λ).mpr hΛfg
  obtain ⟨d, ψ, hψ, hjump⟩ := exists_embedding (A := Λ)
  -- every element of `G` moves points by elements of `Λ`
  have hGΛ : ∀ g ∈ G, ∀ z, g z - z ∈ Λ := by
    intro g hg
    rw [← hcl] at hg
    induction hg using Subgroup.closure_induction with
    | mem s hs => exact hang s hs
    | one => intro z; simp
    | mul g h _ _ hg hh =>
      intro z
      have := Λ.add_mem (hg (h z)) (hh z)
      simpa [Equiv.Perm.mul_apply] using this
    | inv g _ hg =>
      intro z
      have := Λ.neg_mem (hg (g⁻¹ z))
      simpa using this
  have horb : ∀ y ∈ MulAction.orbit G x, y - x ∈ Λ := by
    rintro y ⟨g, rfl⟩
    exact hGΛ g g.2 x
  let f : UnitAddCircle → Fin d → ℤ := fun y => if h : y - x ∈ Λ then ψ ⟨y - x, h⟩ else 0
  have hf : ∀ y (h : y - x ∈ Λ), f y = ψ ⟨y - x, h⟩ := fun y h => dif_pos h
  -- the jumps
  let J : Set Λ := {a | ∃ s ∈ S, (a : UnitAddCircle) ∈ angles s}
  have hJfin : J.Finite := by
    have h1 : (⋃ s ∈ (S : Set (Equiv.Perm UnitAddCircle)), angles s).Finite :=
      S.finite_toSet.biUnion fun g hg => angles_finite_of_mem_IET (hG (hS g hg))
    refine (h1.preimage Subtype.val_injective.injOn).subset ?_
    rintro a ⟨s, hs, ha⟩
    exact Set.mem_biUnion (x := s) hs ha
  choose Lf hLf using hjump
  obtain ⟨L, hL⟩ := (hJfin.image Lf).bddAbove
  refine ⟨d, f, L, ?_, ?_⟩
  · intro a ha b hb hab
    rw [hf a (horb a ha), hf b (horb b hb)] at hab
    have := congrArg Subtype.val (hψ hab)
    simpa using this
  · intro y hy s hs i
    have hy' := horb y hy
    have hsy : s y - x ∈ Λ := by
      have := Λ.add_mem hy' (hang s hs y)
      simpa using this
    let a : Λ := ⟨s y - y, hang s hs y⟩
    have haJ : a ∈ J := ⟨s, hs, y, rfl⟩
    have e : (⟨s y - x, hsy⟩ : Λ) = ⟨y - x, hy'⟩ + a := Subtype.ext (by simp [a])
    rw [hf _ hsy, hf _ hy', e]
    exact (hLf a _ i).trans (by exact_mod_cast hL ⟨a, haJ, rfl⟩)


lemma image_map_eq_preimage {Z : Type*} (e : Equiv.Perm Z) (S : Set (Finset Z)) :
    (fun E => E.map e.toEmbedding) '' S = (fun E => E.map e.symm.toEmbedding) ⁻¹' S := by
  ext E
  constructor
  · rintro ⟨F, hF, rfl⟩
    simp only [Set.mem_preimage, Finset.map_map]
    convert hF
    ext z; simp
  · intro hE
    refine ⟨_, hE, ?_⟩
    ext z; simp

/-- Pulling extensive amenability back along an injective map that intertwines each element of
`G` with some element of `W`. -/
theorem isExtensivelyAmenable_of_injective {G X W Y : Type*} [Group G] [MulAction G X]
    [Group W] [MulAction W Y] (hW : IsExtensivelyAmenable W Y) (g : X → Y)
    (hg : Function.Injective g) (hint : ∀ a : G, ∃ w : W, ∀ y : X, g (a • y) = w • g y) :
    IsExtensivelyAmenable G X := by
  classical
  obtain ⟨m, ⟨hm0, hmadd⟩, -, hmuniv, hminv, hmE⟩ := hW
  have hmono : ∀ s t : Set (Finset Y), s ⊆ t → m s ≤ m t := by
    intro s t hst
    have := hmadd s (t \ s) Set.disjoint_sdiff_right
    rw [Set.union_sdiff_cancel hst] at this
    rw [this]; exact le_self_add
  let Φ : Finset Y → Finset X := fun E => E.preimage g hg.injOn
  refine ⟨fun S => m (Φ ⁻¹' S), ⟨by simpa using hm0, fun s t hst => ?_⟩, ?_, ?_, ?_, ?_⟩
  · show m (Φ ⁻¹' (s ∪ t)) = m (Φ ⁻¹' s) + m (Φ ⁻¹' t)
    rw [Set.preimage_union]
    exact hmadd _ _ (hst.preimage Φ)
  · simpa using hmuniv
  · simpa using hmuniv
  · intro a S
    obtain ⟨w, hw⟩ := hint a
    show m (Φ ⁻¹' _) = m (Φ ⁻¹' S)
    rw [image_map_eq_preimage, ← hminv w (Φ ⁻¹' S), image_map_eq_preimage]
    congr 1
    ext E
    simp only [Set.mem_preimage]
    congr! 1
    ext z
    simp [Φ, Finset.mem_preimage, Finset.mem_map_equiv, hw]
  · intro E₀ _
    refine le_antisymm ?_ ?_
    · rw [← hmuniv]; exact hmono _ _ (Set.subset_univ _)
    · rw [← hmE (E₀.image g) (Set.subset_univ _)]
      apply hmono
      intro F hF z hz
      simp only [Set.mem_ofPred_eq] at hF
      simp only [Φ, Finset.mem_preimage]
      exact hF (Finset.mem_image_of_mem g hz)

end IETG

theorem chk_isAmenable_IET_of_forall_isExtensivelyAmenable_wobbling
    (h : ∀ d : ℕ, IsExtensivelyAmenable ↥(wobbling (Fin d → ℤ)) (Fin d → ℤ)) :
    Garrido.IsAmenable ↥IET := by
  classical
  rw [JMMS.isAmenable_iff_isExtensivelyAmenable_of_le_IET IET le_rfl]
  refine ((JMMS.isExtensivelyAmenable_tfae (G := ↥IET) (X := UnitAddCircle)).out 0 1).mpr ?_
  intro H hH x
  have hHfg : Group.FG ↥H := (Group.fg_iff_subgroup_fg H).mpr hH
  obtain ⟨S1, hS1cl⟩ := hHfg.out
  let φ : ↥H →* Equiv.Perm UnitAddCircle := IET.subtype.comp H.subtype
  set K := φ.range with hK
  set SK : Finset (Equiv.Perm UnitAddCircle) := S1.image φ with hSK
  have hKle : K ≤ IET := by
    rintro _ ⟨h, rfl⟩
    exact (h : ↥IET).2
  have hSKK : ∀ s ∈ SK, s ∈ K := by
    intro s hs
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hs
    exact ⟨t, rfl⟩
  have hSKcl : Subgroup.closure (SK : Set (Equiv.Perm UnitAddCircle)) = K := by
    rw [hSK, Finset.coe_image, ← MonoidHom.map_closure, hS1cl, hK, MonoidHom.range_eq_map]
  obtain ⟨d, f, L, hinj, hL⟩ := IETG.exists_embedding_orbit K hKle SK hSKK hSKcl x
  -- every element of `K` moves points of the orbit a bounded distance
  have hKorb : ∀ k ∈ K, ∀ y ∈ MulAction.orbit K x, k y ∈ MulAction.orbit K x := by
    intro k hk y hy
    have : (⟨k, hk⟩ : K) • y ∈ MulAction.orbit K x := MulAction.mem_orbit_of_mem_orbit _ hy
    exact this
  have hbd : ∀ k ∈ K, ∃ C : ℝ, ∀ y ∈ MulAction.orbit K x, dist (f (k y)) (f y) ≤ C := by
    intro k hk
    rw [← hSKcl] at hk
    induction hk using Subgroup.closure_induction with
    | mem s hs =>
      refine ⟨L, fun y hy => ?_⟩
      rw [dist_pi_le_iff (Nat.cast_nonneg L)]
      intro i
      rw [Int.dist_eq]
      exact_mod_cast hL y hy s hs i
    | one => exact ⟨0, fun y _ => by simp⟩
    | mul k₁ k₂ hk₁ hk₂ ih₁ ih₂ =>
      obtain ⟨C₁, hC₁⟩ := ih₁
      obtain ⟨C₂, hC₂⟩ := ih₂
      refine ⟨C₁ + C₂, fun y hy => ?_⟩
      rw [hSKcl] at hk₂
      calc dist (f ((k₁ * k₂) y)) (f y) ≤ dist (f (k₁ (k₂ y))) (f (k₂ y)) + dist (f (k₂ y)) (f y) :=
            dist_triangle _ _ _
        _ ≤ C₁ + C₂ := add_le_add (hC₁ _ (hKorb k₂ hk₂ y hy)) (hC₂ y hy)
    | inv k hk ih =>
      obtain ⟨C, hC⟩ := ih
      refine ⟨C, fun y hy => ?_⟩
      rw [hSKcl] at hk
      have hy' : k⁻¹ y ∈ MulAction.orbit K x := hKorb k⁻¹ (K.inv_mem hk) y hy
      have := hC _ hy'
      rw [dist_comm]
      simpa using this
  have horb : ∀ y : MulAction.orbit (↥H) x, (y : UnitAddCircle) ∈ MulAction.orbit K x := by
    rintro ⟨y, h, rfl⟩
    exact ⟨⟨φ h, h, rfl⟩, rfl⟩
  let g : MulAction.orbit (↥H) x → Fin d → ℤ := fun y => f y
  have hg : Function.Injective g := fun a b hab =>
    Subtype.ext (hinj (horb a) (horb b) hab)
  refine IETG.isExtensivelyAmenable_of_injective (h d) g hg fun a => ?_
  obtain ⟨C, hC⟩ := hbd (φ a) ⟨a, rfl⟩
  let w : Equiv.Perm (Fin d → ℤ) := (MulAction.toPerm a).extendDomain (Equiv.ofInjective g hg)
  have hw : ∀ y, w (g y) = g (a • y) := by
    intro y
    have := Equiv.Perm.extendDomain_apply_image (MulAction.toPerm a) (Equiv.ofInjective g hg) y
    simpa [w] using this
  refine ⟨⟨w, ⟨max C 0, fun z => ?_⟩⟩, fun y => (hw y).symm⟩
  by_cases hz : z ∈ Set.range g
  · obtain ⟨y, rfl⟩ := hz
    rw [hw]
    exact (hC y (horb y)).trans (le_max_left _ _)
  · rw [Equiv.Perm.extendDomain_apply_not_subtype _ _ hz, dist_self]
    exact le_max_right _ _

end Garban

end

open IntervalExchange
open Garban in
theorem solution
    (h : ∀ d : ℕ, IsExtensivelyAmenable ↥(wobbling (Fin d → ℤ)) (Fin d → ℤ)) :
    Garrido.IsAmenable ↥IET :=
  Garban.chk_isAmenable_IET_of_forall_isExtensivelyAmenable_wobbling h
