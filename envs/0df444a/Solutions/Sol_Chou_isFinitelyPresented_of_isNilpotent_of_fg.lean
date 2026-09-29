-- Prove2me | solution 1 for Chou.isFinitelyPresented_of_isNilpotent_of_fg
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-24T19:25:00.395497+00:00
-- url     : https://prove2.me/submissions/a779dba9-60e6-472f-8b7d-a226810b98ba

import Theorems.Thm_GroupFiniteness_isFinitelyPresented_of_extension
import Definitions.Def_MilnorWolf_Growth
import Mathlib

/-!
# Polycyclic groups (Wolf, Proposition 4.1 (1), p. 433)

Basic closure properties of `MilnorWolf.IsPolycyclic`: trivial groups and cyclic groups are
polycyclic, the notion is invariant under isomorphism, finitely generated abelian groups are
polycyclic, and an extension of a polycyclic group by a polycyclic group is polycyclic
(Rosenblatt's Remark 4.3).  Polycyclic groups are finitely generated and finitely presented.

The `Fin (t + 1)`-indexed normal series of the published definition is replaced, for the duration
of the proofs, by the `ℕ`-indexed characterisation `MilnorWolf.Lib.IsPolyChain`: a chain
`A : ℕ → Subgroup G` with `A 0 = ⊤`, eventually `⊥`, and each step normal with cyclic quotient.
-/

universe u v

namespace MilnorWolf
namespace Lib

open Function Subgroup

/-! ### One step of a normal series -/

/-- One step `H ⊆ K` of a normal series: `H ≤ K`, `H` is normal in `K`, and `K/H` is cyclic. -/
def IsCyclicStep {G : Type*} [Group G] (H K : Subgroup G) : Prop :=
  H ≤ K ∧ ∃ _ : (H.subgroupOf K).Normal, IsCyclic (K ⧸ H.subgroupOf K)

/-- Transport of "normal with cyclic quotient" along a surjection, by pulling the subgroup back. -/
theorem normal_isCyclic_comap {A B : Type*} [Group A] [Group B] (φ : A →* B)
    (hφ : Surjective φ) {Q : Subgroup B} (hn : Q.Normal) (hc : IsCyclic (B ⧸ Q)) :
    ∃ _ : (Q.comap φ).Normal, IsCyclic (A ⧸ Q.comap φ) := by
  have : Q.Normal := hn
  have hn' : (Q.comap φ).Normal := hn.comap φ
  refine ⟨hn', ?_⟩
  have hker : Q.comap φ = ((QuotientGroup.mk' Q).comp φ).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  have hs : Surjective ((QuotientGroup.mk' Q).comp φ) :=
    (QuotientGroup.mk'_surjective Q).comp hφ
  have e : A ⧸ Q.comap φ ≃* B ⧸ Q :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ hs)
  exact isCyclic_of_surjective e.symm e.symm.surjective

/-- The restriction of `f : G →* H` to the preimage of `K`. -/
def restrictComap {G H : Type*} [Group G] [Group H] (f : G →* H) (K : Subgroup H) :
    ↥(K.comap f) →* ↥K :=
  (f.comp (K.comap f).subtype).codRestrict K (fun x => Subgroup.mem_comap.mp x.2)

@[simp] theorem restrictComap_coe {G H : Type*} [Group G] [Group H] (f : G →* H) (K : Subgroup H)
    (x : ↥(K.comap f)) : ((restrictComap f K x : ↥K) : H) = f (x : G) := rfl

theorem restrictComap_surjective {G H : Type*} [Group G] [Group H] {f : G →* H}
    (hf : Surjective f) (K : Subgroup H) : Surjective (restrictComap f K) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨⟨x, by simpa using hy⟩, rfl⟩

/-- A step of a normal series pulls back along a surjection. -/
theorem IsCyclicStep.comap {G H : Type*} [Group G] [Group H] {f : G →* H} (hf : Surjective f)
    {K₂ K₁ : Subgroup H} (h : IsCyclicStep K₂ K₁) :
    IsCyclicStep (K₂.comap f) (K₁.comap f) := by
  obtain ⟨hle, hnorm, hcyc⟩ := h
  refine ⟨Subgroup.comap_mono hle, ?_⟩
  have hkey : (K₂.subgroupOf K₁).comap (restrictComap f K₁) =
      (K₂.comap f).subgroupOf (K₁.comap f) := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  have := normal_isCyclic_comap (restrictComap f K₁) (restrictComap_surjective hf K₁)
    hnorm hcyc
  rwa [hkey] at this

/-- A step of a normal series pushes forward along an injection. -/
theorem IsCyclicStep.map {G H : Type*} [Group G] [Group H] {f : G →* H} (hf : Injective f)
    {H₂ H₁ : Subgroup G} (h : IsCyclicStep H₂ H₁) :
    IsCyclicStep (H₂.map f) (H₁.map f) := by
  obtain ⟨hle, hnorm, hcyc⟩ := h
  refine ⟨Subgroup.map_mono hle, ?_⟩
  have hcoe : ∀ x : ↥(H₁.map f),
      f (((Subgroup.equivMapOfInjective H₁ f hf).symm x : ↥H₁) : G) = (x : H) := by
    intro x
    conv_rhs => rw [← MulEquiv.apply_symm_apply (Subgroup.equivMapOfInjective H₁ f hf) x]
    exact (Subgroup.coe_equivMapOfInjective_apply H₁ f hf _).symm
  have hkey : (H₂.subgroupOf H₁).comap
      ((Subgroup.equivMapOfInjective H₁ f hf).symm : ↥(H₁.map f) →* ↥H₁) =
      (H₂.map f).subgroupOf (H₁.map f) := by
    ext x
    simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    rw [← hcoe x]
    exact (Subgroup.mem_map_iff_mem hf).symm
  have := normal_isCyclic_comap
    ((Subgroup.equivMapOfInjective H₁ f hf).symm : ↥(H₁.map f) →* ↥H₁)
    (Subgroup.equivMapOfInjective H₁ f hf).symm.surjective hnorm hcyc
  rwa [hkey] at this

theorem IsCyclicStep.congr {G : Type*} [Group G] {H K H' K' : Subgroup G} (h : IsCyclicStep H K)
    (e₁ : H = H') (e₂ : K = K') : IsCyclicStep H' K' := e₁ ▸ e₂ ▸ h

/-- The trivial step `⊥ ⊆ ⊥`. -/
theorem isCyclicStep_of_eq_bot {G : Type*} [Group G] {H K : Subgroup G} (hH : H = ⊥)
    (hK : K = ⊥) : IsCyclicStep H K := by
  subst hH; subst hK
  have hn : ((⊥ : Subgroup G).subgroupOf ⊥).Normal := by
    rw [Subgroup.subgroupOf_bot_eq_top]; infer_instance
  exact ⟨le_rfl, hn,
    isCyclic_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)⟩

/-- The step `⊥ ⊆ ⊤` of a cyclic group. -/
theorem isCyclicStep_bot_top {G : Type*} [Group G] [IsCyclic G] :
    IsCyclicStep (⊥ : Subgroup G) ⊤ := by
  have hn : ((⊥ : Subgroup G).subgroupOf ⊤).Normal := by
    rw [Subgroup.bot_subgroupOf]; infer_instance
  exact ⟨bot_le, hn,
    isCyclic_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)⟩

/-! ### An `ℕ`-indexed characterisation of `IsPolycyclic` -/

/-- A normal series of `G` indexed by `ℕ`: `A 0 = ⊤`, some `A t = ⊥`, and every step
`A (i+1) ⊆ A i` is normal with cyclic quotient. -/
def IsPolyChain {G : Type*} [Group G] (A : ℕ → Subgroup G) : Prop :=
  A 0 = ⊤ ∧ (∃ t, A t = ⊥) ∧ ∀ i, IsCyclicStep (A (i + 1)) (A i)

theorem isPolycyclic_of_chain {G : Type*} [Group G] {A : ℕ → Subgroup G} (h : IsPolyChain A) :
    IsPolycyclic G := by
  obtain ⟨h0, ⟨t, ht⟩, hstep⟩ := h
  exact ⟨t, fun i => A i.val, h0, ht, fun i => hstep i.val⟩

theorem exists_chain_of_isPolycyclic {G : Type*} [Group G] (h : IsPolycyclic G) :
    ∃ A : ℕ → Subgroup G, IsPolyChain A := by
  obtain ⟨t, A, h0, hlast, hstep⟩ := h
  have hbot : ∀ m, t ≤ m →
      A ⟨min m t, Nat.lt_succ_of_le (min_le_right m t)⟩ = ⊥ := by
    intro m hm
    rw [← hlast]
    exact congrArg A (Fin.ext (by simp [Fin.val_last]; omega))
  refine ⟨fun n => A ⟨min n t, Nat.lt_succ_of_le (min_le_right n t)⟩, ?_, ⟨t, ?_⟩, ?_⟩
  · rw [← h0]; exact congrArg A (Fin.ext (by simp))
  · exact hbot t le_rfl
  · intro i
    rcases lt_or_ge i t with hi | hi
    · refine IsCyclicStep.congr (hstep ⟨i, hi⟩) (congrArg A (Fin.ext ?_))
        (congrArg A (Fin.ext ?_))
      · simp only [Fin.val_succ]; omega
      · simp only [Fin.val_castSucc]; omega
    · exact isCyclicStep_of_eq_bot (hbot (i + 1) (by omega)) (hbot i hi)

/-! ### The basic examples -/

/-- A trivial group is polycyclic. -/
theorem isPolycyclic_of_subsingleton {G : Type*} [Group G] [Subsingleton G] :
    IsPolycyclic G := by
  have hbot : (⊥ : Subgroup G) = ⊤ := by
    ext x
    simp [Subsingleton.elim x 1]
  exact isPolycyclic_of_chain (A := fun _ => ⊥)
    ⟨hbot, ⟨0, rfl⟩, fun _ => isCyclicStep_of_eq_bot rfl rfl⟩

/-- A cyclic group is polycyclic. -/
theorem isPolycyclic_of_isCyclic {G : Type*} [Group G] [IsCyclic G] : IsPolycyclic G := by
  refine isPolycyclic_of_chain (A := fun n => if n = 0 then ⊤ else ⊥) ⟨rfl, ⟨1, rfl⟩, ?_⟩
  intro i
  match i with
  | 0 => exact isCyclicStep_bot_top
  | (j + 1) => exact isCyclicStep_of_eq_bot rfl rfl

/-! ### Extensions -/

/-- Rosenblatt's Remark 4.3: an extension of a polycyclic group by a polycyclic group is
polycyclic. -/
theorem isPolycyclic_of_extension {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (hN : IsPolycyclic N) (hQ : IsPolycyclic (G ⧸ N)) : IsPolycyclic G := by
  obtain ⟨C, hC0, ⟨a, hCa⟩, hCstep⟩ := exists_chain_of_isPolycyclic hN
  obtain ⟨B, hB0, ⟨b0, hBb0⟩, hBstep⟩ := exists_chain_of_isPolycyclic hQ
  obtain ⟨b, hb1, hBb⟩ : ∃ b, 1 ≤ b ∧ B b = ⊥ :=
    ⟨b0 + 1, by omega, le_bot_iff.mp (by rw [← hBb0]; exact (hBstep b0).1)⟩
  have hmkN : (B b).comap (QuotientGroup.mk' N) = N := by
    rw [hBb, MonoidHom.comap_bot, QuotientGroup.ker_mk']
  have hsubN : (C 0).map N.subtype = N := by
    rw [hC0, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  refine isPolycyclic_of_chain
    (A := fun i => if i < b then (B i).comap (QuotientGroup.mk' N)
      else (C (i - b)).map N.subtype) ⟨?_, ⟨b + a, ?_⟩, ?_⟩
  · show (if (0 : ℕ) < b then (B 0).comap (QuotientGroup.mk' N)
      else (C (0 - b)).map N.subtype) = ⊤
    rw [if_pos (by omega : (0 : ℕ) < b), hB0, Subgroup.comap_top]
  · show (if b + a < b then (B (b + a)).comap (QuotientGroup.mk' N)
      else (C (b + a - b)).map N.subtype) = ⊥
    rw [if_neg (by omega), show b + a - b = a by omega, hCa, Subgroup.map_bot]
  · intro i
    show IsCyclicStep
      (if i + 1 < b then (B (i + 1)).comap (QuotientGroup.mk' N)
        else (C (i + 1 - b)).map N.subtype)
      (if i < b then (B i).comap (QuotientGroup.mk' N) else (C (i - b)).map N.subtype)
    rcases lt_or_ge (i + 1) b with h1 | h1
    · rw [if_pos h1, if_pos (by omega : i < b)]
      exact (hBstep i).comap (QuotientGroup.mk'_surjective N)
    · rcases lt_or_ge i b with hi | hi
      · have hib : i + 1 = b := by omega
        rw [if_neg (by omega), if_pos hi, show i + 1 - b = 0 by omega]
        refine IsCyclicStep.congr ((hBstep i).comap (QuotientGroup.mk'_surjective N)) ?_ rfl
        rw [hib, hmkN, hsubN]
      · rw [if_neg (by omega), if_neg (by omega), show i + 1 - b = (i - b) + 1 by omega]
        exact (hCstep (i - b)).map (Subgroup.subtype_injective N)

/-! ### Finitely generated abelian groups -/

theorem isPolycyclic_of_top_eq_bot {G : Type*} [Group G] (h : (⊤ : Subgroup G) = ⊥) :
    IsPolycyclic G := by
  have : Subsingleton G := ⟨fun x y => by
    have hx : x ∈ (⊥ : Subgroup G) := h ▸ Subgroup.mem_top x
    have hy : y ∈ (⊥ : Subgroup G) := h ▸ Subgroup.mem_top y
    rw [Subgroup.mem_bot] at hx hy
    rw [hx, hy]⟩
  exact isPolycyclic_of_subsingleton

/-- Induction on the size of a generating family: an abelian group generated by `n` elements is
polycyclic. -/
theorem isPolycyclic_commGroup_aux (n : ℕ) : ∀ (G : Type u) [CommGroup G] (s : Fin n → G),
    Subgroup.closure (Set.range s) = ⊤ → IsPolycyclic G := by
  induction n with
  | zero =>
    intro G _ s hgen
    refine isPolycyclic_of_top_eq_bot ?_
    rw [← hgen, Set.range_eq_empty, Subgroup.closure_empty]
  | succ n ih =>
    intro G _ s hgen
    set s' : Fin n → G := fun i => s i.succ with hs'
    set N : Subgroup G := Subgroup.closure (Set.range s') with hNdef
    have hmem : ∀ i : Fin n, s' i ∈ N := fun i => Subgroup.subset_closure ⟨i, rfl⟩
    have hNpoly : IsPolycyclic N := by
      refine ih N (fun i => (⟨s' i, hmem i⟩ : ↥N)) ?_
      apply Subgroup.map_injective (Subgroup.subtype_injective N)
      rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      have himg : (N.subtype : ↥N → G) ''
          Set.range (fun i => (⟨s' i, hmem i⟩ : ↥N)) = Set.range s' := by
        rw [← Set.range_comp]; rfl
      rw [himg, ← hNdef]
    have hgen' : Subgroup.closure ((QuotientGroup.mk' N) '' Set.range s) = ⊤ := by
      rw [← MonoidHom.map_closure, hgen]
      exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)
    have hsub : (QuotientGroup.mk' N) '' Set.range s ⊆
        (Subgroup.zpowers ((QuotientGroup.mk' N) (s 0)) : Set (G ⧸ N)) := by
      rintro _ ⟨x, ⟨i, rfl⟩, rfl⟩
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · exact Subgroup.mem_zpowers _
      · have h1 : (QuotientGroup.mk' N) (s j.succ) = 1 :=
          (QuotientGroup.eq_one_iff _).2 (hmem j)
        rw [h1]
        exact Subgroup.one_mem _
    have hle : (⊤ : Subgroup (G ⧸ N)) ≤ Subgroup.zpowers ((QuotientGroup.mk' N) (s 0)) := by
      rw [← hgen']
      exact (Subgroup.closure_le _).2 hsub
    have hcyc : IsCyclic (G ⧸ N) :=
      ⟨⟨(QuotientGroup.mk' N) (s 0), fun x => hle (Subgroup.mem_top x)⟩⟩
    exact isPolycyclic_of_extension N hNpoly isPolycyclic_of_isCyclic

/-- A finitely generated abelian group is polycyclic. -/
theorem isPolycyclic_of_commGroup_of_fg {G : Type*} [CommGroup G] [Group.FG G] :
    IsPolycyclic G := by
  obtain ⟨S, hS⟩ := Group.fg_def.mp ‹Group.FG G›
  have hrange : Set.range (fun i : Fin S.card => ((S.equivFin.symm i : {x // x ∈ S}) : G))
      = (S : Set G) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact (S.equivFin.symm i).2
    · intro hy
      exact ⟨S.equivFin ⟨y, hy⟩, by simp⟩
  exact isPolycyclic_commGroup_aux S.card G _ (by rw [hrange]; exact hS)

/-! ### Polycyclic groups are finitely generated -/

theorem fg_of_isCyclic {C : Type*} [Group C] [IsCyclic C] : Group.FG C := by
  obtain ⟨g, hg⟩ := ‹IsCyclic C›.exists_generator
  refine Group.fg_iff.mpr ⟨{g}, ?_, Set.finite_singleton g⟩
  rw [← Subgroup.zpowers_eq_closure]
  exact eq_top_iff.2 fun x _ => hg x

/-! ### Polycyclic groups are finitely presented -/

/-- A cyclic group is finitely presented. -/
theorem isFinitelyPresented_of_isCyclic {C : Type*} [Group C] [IsCyclic C] :
    Group.IsFinitelyPresented C := by
  obtain ⟨g, hg⟩ := ‹IsCyclic C›.exists_generator
  have hsurj : Function.Surjective (zpowersHom C g) := by
    intro x
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
    exact ⟨Multiplicative.ofAdd m, by simpa using hm⟩
  refine Group.IsFinitelyPresented.of_surjective (zpowersHom C g) hsurj ?_
  have : Group.FG ↥(zpowersHom C g).ker := fg_of_isCyclic
  exact Subgroup.IsFinitelyNormallyGenerated.of_FG _

/-- P. Hall: an extension of a finitely presented group by a finitely presented group is
finitely presented. -/
theorem isFinitelyPresented_of_extension {G : Type*} [Group G] (N : Subgroup G)
    [hNnormal : N.Normal]
    (hN : Group.IsFinitelyPresented N) (hQ : Group.IsFinitelyPresented (G ⧸ N)) :
    Group.IsFinitelyPresented G :=
  by haveI := hN; haveI := hQ; exact GroupFiniteness.isFinitelyPresented_of_extension N


/-- A polycyclic group is finitely presented. -/
theorem isFinitelyPresented_of_isPolycyclic {G : Type*} [Group G] (h : IsPolycyclic G) :
    Group.IsFinitelyPresented G := by
  obtain ⟨A, h0, ⟨t, ht⟩, hstep⟩ := exists_chain_of_isPolycyclic h
  have key : ∀ j : ℕ, Group.IsFinitelyPresented ↥(A (t - j)) := by
    intro j
    induction j with
    | zero =>
      rw [Nat.sub_zero, ht]
      have : Finite ↥(⊥ : Subgroup G) := inferInstance
      infer_instance
    | succ j ihj =>
      rcases le_or_gt t j with hj | hj
      · have hjj : t - (j + 1) = t - j := by omega
        rw [hjj]; exact ihj
      · have he : t - j = (t - (j + 1)) + 1 := by omega
        rw [he] at ihj
        set i := t - (j + 1) with hi
        obtain ⟨hle, hnorm, hcyc⟩ := hstep i
        have hFPP : Group.IsFinitelyPresented ↥((A (i + 1)).subgroupOf (A i)) := by
          have := ihj
          exact Group.IsFinitelyPresented.equiv (Subgroup.subgroupOfEquivOfLe hle).symm
        have hn := hnorm
        have hc := hcyc
        have hFPQ : Group.IsFinitelyPresented (↥(A i) ⧸ (A (i + 1)).subgroupOf (A i)) :=
          isFinitelyPresented_of_isCyclic
        exact isFinitelyPresented_of_extension ((A (i + 1)).subgroupOf (A i)) hFPP hFPQ
  have hfp0 : Group.IsFinitelyPresented ↥(A 0) := by
    have hkt := key t
    rwa [Nat.sub_self] at hkt
  rw [h0] at hfp0
  have := hfp0
  exact Group.IsFinitelyPresented.equiv Subgroup.topEquiv

end Lib
end MilnorWolf

/-!
# A finitely generated nilpotent group is finitely presented (Chou, p. 400)

Chou uses, on p. 400, the standard fact that a finitely generated nilpotent group is finitely
presented: "`C₁` is also finitely generated and hence is finitely presented".  The route taken
here is the classical one: a finitely generated nilpotent group is *polycyclic*
(`MilnorWolf.IsPolycyclic`, Wolf Proposition 4.1 (1)), and a polycyclic group is finitely
presented by `MilnorWolf.Lib.isFinitelyPresented_of_isPolycyclic`.

The substantive content is that every term of the lower central series of a finitely generated
group is finitely generated.  This is proved here from two elementary facts:

* if `G = ⟨S⟩` then `⁅normalClosure X, G⁆` is the normal closure of the finitely many commutators
  `⁅x, s⁆`, `x ∈ X`, `s ∈ S` (`commutator_normalClosure_top`) — so each `lowerCentralSeries ⊤ n`
  is the normal closure of a finite set (`exists_finite_normalClosure_lowerCentralSeries`);
* if `⁅normalClosure X, G⁆ ≤ M` with `M` normal, then `normalClosure X ≤ closure X ⊔ M`
  (`normalClosure_le_closure_sup`), because modulo `M` the conjugates of `X` are the elements
  of `X`.

Applying the second with `M = lowerCentralSeries ⊤ (n + 1)` gives
`lowerCentralSeries ⊤ n = closure X ⊔ lowerCentralSeries ⊤ (n + 1)`, and a downward induction
starting from the vanishing term of a nilpotent group makes every term finitely generated
(`fg_lowerCentralSeries`).  The polycyclicity is then an induction on the nilpotency class over
all groups at once: the last nonzero term `A = lowerCentralSeries ⊤ n` is central, hence abelian,
and finitely generated, so polycyclic; the quotient `G ⧸ A` is finitely generated with
`lowerCentralSeries ⊤ n = ⊥`, so polycyclic by induction; and polycyclicity is closed under
extensions.
-/


namespace Chou
namespace Lib

open Subgroup
open scoped commutatorElement

/-- A finitely generated group with commutative multiplication is polycyclic. -/
theorem isPolycyclic_of_mul_comm {H : Type*} [Group H] [Group.FG H]
    (hcomm : ∀ a b : H, a * b = b * a) : MilnorWolf.IsPolycyclic H := by
  let _ : CommGroup H := { (inferInstance : Group H) with mul_comm := hcomm }
  exact MilnorWolf.Lib.isPolycyclic_of_commGroup_of_fg

/-- If `G` is generated by `S`, then `⁅normalClosure X, G⁆` is the normal closure of the set of
commutators `⁅x, s⁆` with `x ∈ X` and `s ∈ S`. -/
theorem commutator_normalClosure_top {G : Type*} [Group G] {S : Set G}
    (hS : closure S = (⊤ : Subgroup G)) (X : Set G) :
    ⁅normalClosure X, (⊤ : Subgroup G)⁆
      = normalClosure (Set.image2 (fun x s => ⁅x, s⁆) X S) := by
  refine le_antisymm ?_ ?_
  · set K := normalClosure (Set.image2 (fun x s => ⁅x, s⁆) X S) with hK
    set π := QuotientGroup.mk' K with hπ
    have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective K
    -- each `π x`, `x ∈ X`, is central in `G ⧸ K`, because it commutes with the generators
    have hcenter : ∀ x ∈ X, π x ∈ Subgroup.center (G ⧸ K) := by
      intro x hx
      have htop : (⊤ : Subgroup (G ⧸ K)) ≤ Subgroup.centralizer {π x} := by
        rw [← Subgroup.map_top_of_surjective π hsurj, ← hS, MonoidHom.map_closure,
          Subgroup.closure_le]
        rintro y ⟨s, hs, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        rintro h rfl
        rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact Subgroup.subset_normalClosure ⟨x, hx, s, hs, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro g
      exact ((Subgroup.mem_centralizer_iff.mp (htop (Subgroup.mem_top g))) _ rfl).symm
    have hncl : normalClosure (π '' X) ≤ Subgroup.center (G ⧸ K) :=
      Subgroup.normalClosure_le_normal (by rintro y ⟨x, hx, rfl⟩; exact hcenter x hx)
    have hmap : (⁅normalClosure X, (⊤ : Subgroup G)⁆).map π = ⊥ := by
      rw [Subgroup.map_commutator, Subgroup.map_normalClosure _ _ hsurj,
        Subgroup.map_top_of_surjective π hsurj, eq_bot_iff, Subgroup.commutator_le]
      intro a ha b _
      have hac := Subgroup.mem_center_iff.mp (hncl ha)
      rw [Subgroup.mem_bot, commutatorElement_def, ← hac b]
      group
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hmap
    exact hmap
  · refine Subgroup.normalClosure_le_normal ?_
    rintro y ⟨x, hx, s, hs, rfl⟩
    exact Subgroup.commutator_mem_commutator (Subgroup.subset_normalClosure hx)
      (Subgroup.mem_top s)

/-- If `⁅normalClosure X, G⁆ ≤ M` with `M` normal, then `normalClosure X ≤ closure X ⊔ M`:
modulo `M` the normal closure of `X` is generated by the image of `X`. -/
theorem normalClosure_le_closure_sup {G : Type*} [Group G] (X : Set G) (M : Subgroup G)
    [M.Normal] (hM : ⁅normalClosure X, (⊤ : Subgroup G)⁆ ≤ M) :
    normalClosure X ≤ closure X ⊔ M := by
  have hM' : ⁅(⊤ : Subgroup G), normalClosure X⁆ ≤ M := by
    rw [Subgroup.commutator_comm]; exact hM
  have hdef : normalClosure X = closure (Group.conjugatesOfSet X) := rfl
  rw [hdef, Subgroup.closure_le]
  intro y hy
  obtain ⟨x, hx, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hy
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  have hcx : ⁅c, x⁆ ∈ M :=
    hM' (Subgroup.commutator_mem_commutator (Subgroup.mem_top c)
      (Subgroup.subset_normalClosure hx))
  have hy' : y = ⁅c, x⁆ * x := by
    rw [commutatorElement_def, ← hc]; group
  rw [SetLike.mem_coe, hy']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hcx)
    (Subgroup.mem_sup_left (Subgroup.subset_closure hx))

/-- Every term of the lower central series of a group generated by a finite set `S` is the normal
closure of a finite set of iterated commutators of elements of `S`. -/
theorem exists_finite_normalClosure_lowerCentralSeries {G : Type*} [Group G] {S : Set G}
    (hSfin : S.Finite) (hS : closure S = (⊤ : Subgroup G)) (n : ℕ) :
    ∃ X : Set G, X.Finite ∧ normalClosure X = (⊤ : Subgroup G).lowerCentralSeries n := by
  induction n with
  | zero =>
    refine ⟨S, hSfin, ?_⟩
    rw [Subgroup.lowerCentralSeries_zero, eq_top_iff, ← hS, Subgroup.closure_le]
    exact Subgroup.subset_normalClosure
  | succ n ih =>
    obtain ⟨X, hXfin, hX⟩ := ih
    refine ⟨Set.image2 (fun x s => ⁅x, s⁆) X S, Set.Finite.image2 _ hXfin hSfin, ?_⟩
    rw [← commutator_normalClosure_top hS X, hX, Subgroup.lowerCentralSeries_succ]

/-- Each term of the lower central series of a finitely generated group whose lower central series
reaches `⊥` is a finitely generated subgroup. -/
theorem fg_lowerCentralSeries {G : Type*} [Group G] [Group.FG G] {c : ℕ}
    (hc : (⊤ : Subgroup G).lowerCentralSeries c = ⊥) (n : ℕ) :
    ((⊤ : Subgroup G).lowerCentralSeries n).FG := by
  obtain ⟨S, hS, hSfin⟩ := (Subgroup.fg_iff _).mp (Group.fg_def.mp ‹Group.FG G›)
  have key : ∀ j : ℕ, ((⊤ : Subgroup G).lowerCentralSeries (c - j)).FG := by
    intro j
    induction j with
    | zero => rw [Nat.sub_zero, hc]; exact Subgroup.FG.bot
    | succ j ihj =>
      rcases le_or_gt c j with hj | hj
      · rw [show c - (j + 1) = c - j by omega]; exact ihj
      · rw [show c - j = (c - (j + 1)) + 1 by omega] at ihj
        set k := c - (j + 1) with hk
        obtain ⟨X, hXfin, hX⟩ := exists_finite_normalClosure_lowerCentralSeries hSfin hS k
        have hstep : (⊤ : Subgroup G).lowerCentralSeries k
            = closure X ⊔ (⊤ : Subgroup G).lowerCentralSeries (k + 1) := by
          refine le_antisymm ?_ ?_
          · rw [← hX]
            refine normalClosure_le_closure_sup X _ ?_
            rw [hX]
            exact le_of_eq (Subgroup.lowerCentralSeries_succ ⊤ k).symm
          · refine sup_le ?_ (Subgroup.lowerCentralSeries_antitone ⊤ (Nat.le_succ k))
            rw [← hX, Subgroup.closure_le]
            exact Subgroup.subset_normalClosure
        rw [hstep]
        exact Subgroup.FG.sup ((Subgroup.fg_iff _).mpr ⟨X, rfl, hXfin⟩) ihj
  rcases le_or_gt c n with hn | hn
  · have hbot : (⊤ : Subgroup G).lowerCentralSeries n = ⊥ := by
      rw [eq_bot_iff, ← hc]; exact Subgroup.lowerCentralSeries_antitone ⊤ hn
    rw [hbot]; exact Subgroup.FG.bot
  · have hk := key (c - n)
    rwa [show c - (c - n) = n by omega] at hk

/-- A finitely generated group whose lower central series vanishes at step `n` is polycyclic.
The statement is universally quantified over the group so that the inductive hypothesis applies to
the quotient `G ⧸ lowerCentralSeries ⊤ n`. -/
theorem isPolycyclic_of_lowerCentralSeries_eq_bot :
    ∀ (n : ℕ) {G : Type u} [Group G] [Group.FG G],
      (⊤ : Subgroup G).lowerCentralSeries n = ⊥ → MilnorWolf.IsPolycyclic G := by
  intro n
  induction n with
  | zero =>
    intro G _ _ h
    exact MilnorWolf.Lib.isPolycyclic_of_top_eq_bot (by simpa using h)
  | succ n ih =>
    intro G _ _ h
    set A := (⊤ : Subgroup G).lowerCentralSeries n with hA
    have hAnorm : A.Normal := by rw [hA]; infer_instance
    -- `A` is central, because `⁅A, G⁆ = lowerCentralSeries ⊤ (n + 1) = ⊥`
    have hcentral : ∀ a ∈ A, ∀ g : G, a * g = g * a := by
      intro a ha g
      have hmem : ⁅a, g⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries (n + 1) :=
        Subgroup.commutator_mem_commutator ha (Subgroup.mem_top g)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hmem
    -- the quotient is finitely generated and its lower central series vanishes one step earlier
    have hQfg : Group.FG (G ⧸ A) := QuotientGroup.fg A
    have hQlcs : (⊤ : Subgroup (G ⧸ A)).lowerCentralSeries n = ⊥ := by
      have hmap := Subgroup.map_lowerCentralSeries (⊤ : Subgroup G) (QuotientGroup.mk' A) n
      rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective A)] at hmap
      rw [← hmap, ← hA, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    have hQ : MilnorWolf.IsPolycyclic (G ⧸ A) := ih hQlcs
    -- `A` is finitely generated, hence abelian and finitely generated, hence polycyclic
    have hAfg : Group.FG A := by
      refine (Group.fg_iff_subgroup_fg A).mpr ?_
      rw [hA]
      exact fg_lowerCentralSeries h n
    have hAcomm : ∀ a b : A, a * b = b * a := by
      intro a b
      exact Subtype.ext (hcentral a.1 a.2 b.1)
    exact MilnorWolf.Lib.isPolycyclic_of_extension A (isPolycyclic_of_mul_comm hAcomm) hQ

/-- A finitely generated nilpotent group is polycyclic. -/
theorem isPolycyclic_of_isNilpotent_of_fg {G : Type*} [Group G] [Group.FG G]
    [Group.IsNilpotent G] : MilnorWolf.IsPolycyclic G := by
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp ‹Group.IsNilpotent G›
  exact isPolycyclic_of_lowerCentralSeries_eq_bot n hn

/-- Chou, p. 400 (external): a finitely generated nilpotent group is finitely presented. -/
theorem isFinitelyPresented_of_isNilpotent_of_fg' {G : Type*} [Group G] [Group.FG G]
    [Group.IsNilpotent G] : Group.IsFinitelyPresented G :=
  MilnorWolf.Lib.isFinitelyPresented_of_isPolycyclic isPolycyclic_of_isNilpotent_of_fg

end Lib
end Chou

open Chou

theorem solution {G : Type*} [Group G] [Group.FG G] [Group.IsNilpotent G] :
    Group.IsFinitelyPresented G :=
  Chou.Lib.isFinitelyPresented_of_isNilpotent_of_fg'
