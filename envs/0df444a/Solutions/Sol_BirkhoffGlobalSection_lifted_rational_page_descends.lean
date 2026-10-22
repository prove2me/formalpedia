-- Prove2me | solution 1 for BirkhoffGlobalSection.lifted_rational_page_descends
-- status  : ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-26T18:20:46.584399+00:00
-- url     : https://prove2.me/submissions/62fda9fa-0586-4bf7-a8b4-1f8b6c3daec9

import Definitions.Def_BirkhoffGlobalSection_LiftedRationalPage
import Theorems.Thm_BirkhoffGlobalSection_antipodal_quotient_dynamics_continuous
import Theorems.Thm_BirkhoffGlobalSection_antipodal_double_cover_descends_to_prime_binding
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic

open BirkhoffGlobalSection Topology Set
open scoped ContDiff

set_option autoImplicit false

private lemma quotient_eq {μ c : ℝ} (x y : LeftEnergyState μ c) :
    toAntipodalQuotient x = toAntipodalQuotient y ↔
      (x : Phase) = (y : Phase) ∨ (x : Phase) = -(y : Phase) :=
  Quotient.eq

private lemma quotient_continuous {μ c : ℝ} :
    Continuous (toAntipodalQuotient : LeftEnergyState μ c → AntipodalQuotientState μ c) :=
  continuous_quotient_mk'

private lemma quotient_hausdorff {μ c : ℝ}
    (hinv : IsAntipodallyInvariantComponent μ c) : T2Space (AntipodalQuotientState μ c) := by
  let n : LeftEnergyState μ c → LeftEnergyState μ c :=
    fun s => ⟨-(s : Phase), (hinv s).mp s.property⟩
  have hn : Continuous n := continuous_subtype_val.neg.subtype_mk _
  have hopen : IsOpenMap (toAntipodalQuotient :
      LeftEnergyState μ c → AntipodalQuotientState μ c) := by
    intro V hV
    apply isQuotientMap_quotient_mk'.isOpen_preimage.mp
    have heq : toAntipodalQuotient ⁻¹' (toAntipodalQuotient '' V) = V ∪ n ⁻¹' V := by
      ext x
      constructor
      · rintro ⟨y, hy, hxy⟩
        rcases (quotient_eq y x).mp hxy with h | h
        · exact Or.inl (Subtype.ext h ▸ hy)
        · have he : y = n x := Subtype.ext h
          exact Or.inr (show n x ∈ V by rw [← he]; exact hy)
      · rintro (hx | hx)
        · exact ⟨x, hx, rfl⟩
        · exact ⟨n x, hx, (quotient_eq (n x) x).mpr (Or.inr rfl)⟩
    change IsOpen (toAntipodalQuotient ⁻¹' (toAntipodalQuotient '' V))
    rw [heq]
    exact hV.union (hV.preimage hn)
  have hq : IsOpenQuotientMap (toAntipodalQuotient :
      LeftEnergyState μ c → AntipodalQuotientState μ c) :=
    ⟨fun x => Quotient.exists_rep x, quotient_continuous, hopen⟩
  apply (t2Space_iff_of_isOpenQuotientMap hq).mpr
  have heq : {q : LeftEnergyState μ c × LeftEnergyState μ c |
      toAntipodalQuotient q.1 = toAntipodalQuotient q.2} =
      {q | (q.1 : Phase) = (q.2 : Phase)} ∪
      {q | (q.1 : Phase) = -(q.2 : Phase)} := by
    ext q
    exact quotient_eq q.1 q.2
  rw [heq]
  exact (isClosed_eq (continuous_subtype_val.comp continuous_fst)
    (continuous_subtype_val.comp continuous_snd)).union
    (isClosed_eq (continuous_subtype_val.comp continuous_fst)
      (continuous_subtype_val.comp continuous_snd).neg)

/-- A closed map is an embedding on any subset all of whose fibers are singletons. -/
private lemma embedding_of_singleton_fibers {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) (S : Set X)
    (hf : Continuous f) (hclosed : IsClosedMap f)
    (hsingle : ∀ x ∈ S, ∀ y, f x = f y → x = y) :
    IsEmbedding (fun x : S => f x) := by
  refine ⟨⟨?_⟩, ?_⟩
  · refine (hf.comp continuous_subtype_val).le_induced.antisymm fun V hV => ?_
    obtain ⟨W, hW, hWV⟩ := isOpen_induced_iff.mp hV
    refine ⟨(f '' Wᶜ)ᶜ, (hclosed _ hW.isClosed_compl).isOpen_compl, ?_⟩
    rw [← hWV]
    ext x
    change (f x ∉ f '' Wᶜ) ↔ (x : X) ∈ W
    constructor
    · intro h
      by_contra hx
      exact h ⟨x, hx, rfl⟩
    · intro hx ⟨y, hy, heq⟩
      exact hy (hsingle x x.property y heq.symm ▸ hx)
  · intro x y h
    exact Subtype.ext (hsingle x x.property y h)

private lemma compact_disk : IsCompact closedUnitDisk := by
  have hc : IsClosed closedUnitDisk := by
    apply isClosed_le _ continuous_const
    unfold planeNormSq
    fun_prop
  apply (isCompact_closedBall (0 : Plane) 1).of_isClosed_subset hc
  intro u hu
  rw [Metric.mem_closedBall, dist_zero_right,
    pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
  intro i
  change u 0 ^ 2 + u 1 ^ 2 ≤ 1 at hu
  have h0 : |u 0| ≤ 1 := abs_le_of_sq_le_sq (by nlinarith [sq_nonneg (u 1)]) (by norm_num)
  have h1 : |u 1| ≤ 1 := abs_le_of_sq_le_sq (by nlinarith [sq_nonneg (u 0)]) (by norm_num)
  fin_cases i
  · exact h0
  · exact h1

theorem solution {μ c : ℝ} (φ : Flow ℝ (LeftEnergyState μ c))
    (hanti : IsAntipodallyEquivariantFlow μ c φ)
    (hinv : IsAntipodallyInvariantComponent μ c)
    (hfree : IsAntipodallyFreeComponent μ c)
    (γ : PeriodicOrbit φ) (hdouble : IsAntipodalDoubleCover φ γ)
    (P : LiftedRationalPage φ γ) :
    RationalDiskLikeGlobalSurfaceOfSection φ hanti γ := by
  let : T2Space (AntipodalQuotientState μ c) := quotient_hausdorff hinv
  let : CompactSpace ClosedDiskPoint := isCompact_iff_compactSpace.mp compact_disk
  have hpage : Continuous (fun u : ClosedDiskPoint => P.page u) :=
    continuousOn_iff_continuous_domRestrict.mp
      (fun u hu => (P.smooth u hu).continuousAt.continuousWithinAt)
  have hqpage : Continuous (quotientDiskPage P.page P.mapsTo) :=
    quotient_continuous.comp (hpage.subtype_mk (fun u => P.mapsTo u u.property))
  have hfib (u v : ClosedDiskPoint) :
      quotientDiskPage P.page P.mapsTo u = quotientDiskPage P.page P.mapsTo v ↔
        (u : Plane) = (v : Plane) ∨
          (u ∈ closedDiskBoundary ∧ v ∈ closedDiskBoundary ∧ (v : Plane) = -(u : Plane)) := by
    unfold quotientDiskPage
    rw [quotient_eq]
    constructor
    · rintro (h | h)
      · exact Or.inl (P.injective u.property v.property h)
      · exact Or.inr ((P.antipodal_fibers u u.property v v.property).mp h)
    · rintro (h | h)
      · exact Or.inl (congrArg P.page h)
      · exact Or.inr ((P.antipodal_fibers u u.property v v.property).mpr h)
  have hemb : IsEmbedding (quotientDiskInteriorPage P.page P.mapsTo) := by
    apply embedding_of_singleton_fibers (quotientDiskPage P.page P.mapsTo)
      closedDiskInterior hqpage hqpage.isClosedMap
    intro u hu v heq
    rcases (hfib u v).mp heq with h | h
    · exact Subtype.ext h
    · have hlt : planeNormSq u < 1 := hu
      have he : planeNormSq u = 1 := h.1
      linarith
  have hboundary : quotientDiskPage P.page P.mapsTo '' closedDiskBoundary =
      quotientOrbitSet hanti γ := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hm : P.page u ∈ orbitSet γ := P.boundary ▸ ⟨u, hu, rfl⟩
      obtain ⟨t, ht⟩ := hm
      exact ⟨t, congrArg toAntipodalQuotient (Subtype.ext ht)⟩
    · rintro ⟨t, rfl⟩
      have hm : ((φ t γ.point : LeftEnergyState μ c) : Phase) ∈ P.page '' unitCircle :=
        P.boundary.symm ▸ ⟨t, rfl⟩
      obtain ⟨u, hu, he⟩ := hm
      refine ⟨⟨u, ?_⟩, hu, congrArg toAntipodalQuotient (Subtype.ext he)⟩
      exact le_of_eq hu
  refine ⟨hinv, hfree, antipodal_quotient_dynamics_continuous φ hanti hinv hfree,
    antipodal_double_cover_descends_to_prime_binding φ hanti hinv hfree γ hdouble,
    P.page, P.mapsTo, P.smooth, P.injective, P.immersion, P.transverse, P.boundary,
    hqpage, hemb, hfib, hboundary, ?_⟩
  intro x hx
  obtain ⟨s, rfl⟩ := Quotient.exists_rep x
  have hs : (s : Phase) ∉ orbitSet γ := by
    rintro ⟨t, ht⟩
    exact hx ⟨t, congrArg toAntipodalQuotient (Subtype.ext ht)⟩
  have hh := P.returns s hs
  have hhit (t : ℝ) (u : Plane) (hu : u ∈ openUnitDisk)
      (he : ((φ t s : LeftEnergyState μ c) : Phase) = P.page u ∨
        ((φ t s : LeftEnergyState μ c) : Phase) = -P.page u) :
      quotientTimeMap φ hanti t (toAntipodalQuotient s) ∈
        quotientDiskPage P.page P.mapsTo '' closedDiskInterior := by
    have hud : u ∈ closedUnitDisk := (show planeNormSq u < 1 from hu).le
    refine ⟨⟨u, hud⟩, hu, ?_⟩
    exact ((quotient_eq (φ t s) ⟨P.page u, P.mapsTo u hud⟩).mpr he).symm
  constructor
  · intro R
    obtain ⟨t, ht, u, hu, he⟩ := hh.1 R
    exact ⟨t, ht, hhit t u hu he⟩
  · intro R
    obtain ⟨t, ht, u, hu, he⟩ := hh.2 R
    exact ⟨t, ht, hhit t u hu he⟩
