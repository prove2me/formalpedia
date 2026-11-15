-- Prove2me | solution 1 for DiazModulus.remond_commuting_end
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T10:37:34.738205+00:00
-- url     : https://prove2.me/submissions/bb6466b2-30f4-495d-8e81-e22caffc9b33

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # Rémond's lemma on commuting subspaces of endomorphisms

Let `U, V` be subspaces of `End E` (`dim E = n`) with `ab = ba` for `a ∈ U`, `b ∈ V`; we show
`dim U + dim V ≤ n² + 1` by strong induction on `n`. Replacing `(U, V)` by `(U ∩ V, U + V)` keeps the sum of
dimensions and the commuting property, so we may assume `U ⊆ V`. If `U ⊆ ℂ·1` then `dim U ≤ 1` and
`dim V ≤ n²`. Otherwise pick `m ∈ U` outside `ℂ·1`, an eigenvalue `λ` of `m` and `F = ker(m − λ)`, so
`0 ≠ F ≠ E`. Everything commuting with `m` preserves `F`; this covers `V`, and `U ⊆ V`. Restriction to `F` and
the induced map on `E/F` are multiplicative, so the images `U′, V′ ⊆ End F` and `U″, V″ ⊆ End(E/F)` commute,
and induction bounds `dim U′ + dim V′ ≤ f² + 1`, `dim U″ + dim V″ ≤ (n − f)² + 1`. An `F`-stable map killed by
both lies in `K₀ = {a : a(F) = 0, a(E) ⊆ F} ≅ Hom(E/F, F)`, of dimension at most `f(n − f)`; two applications of
rank–nullity give `dim U ≤ dim U″ + r + k` with `r ≤ dim U′` and `k ≤ dim K₀`, and likewise for `V`. This already
gives `n² + 2`. To reach `n² + 1`: if `r = 0` we use `dim V′ ≤ f²` instead of induction on `F`; if `V` misses
part of `K₀` the count for `V` drops by one; otherwise `K₀ ⊆ V` and some `a ∈ U` has `a(E) ⊆ F`, `a(y) ≠ 0`
for a `y ∈ F`, and then `b = χ(x̄)·y ∈ K₀` (for a linear form `χ ≠ 0` on `E/F`) satisfies `ab ≠ 0 = ba`. -/

namespace RC3_RCE
open DiazModulus Module

universe u

variable {E : Type u} [AddCommGroup E] [Module ℂ E]

/-- Restriction to an `F`-stable subspace, as a linear map on `U`. -/
def resU (U : Submodule ℂ (End ℂ E)) (F : Submodule ℂ E) (hU : ∀ a ∈ U, ∀ x ∈ F, a x ∈ F) :
    U →ₗ[ℂ] End ℂ F where
  toFun a := (a : End ℂ E).restrict (hU a a.2)
  map_add' a b := by ext; simp [LinearMap.restrict_apply]
  map_smul' c a := by ext; simp [LinearMap.restrict_apply]

theorem resU_apply (U : Submodule ℂ (End ℂ E)) (F : Submodule ℂ E) (hU : ∀ a ∈ U, ∀ x ∈ F, a x ∈ F)
    (a : U) (x : F) : ((resU U F hU a x : F) : E) = (a : End ℂ E) x := rfl

/-- The induced map on `E ⧸ F`, as a linear map on `U`. -/
def quoU (U : Submodule ℂ (End ℂ E)) (F : Submodule ℂ E) (hU : ∀ a ∈ U, ∀ x ∈ F, a x ∈ F) :
    U →ₗ[ℂ] End ℂ (E ⧸ F) where
  toFun a := F.mapQ F (a : End ℂ E) (fun x hx => hU a a.2 x hx)
  map_add' a b := by ext; simp
  map_smul' c a := by ext; simp

theorem quoU_apply (U : Submodule ℂ (End ℂ E)) (F : Submodule ℂ E) (hU : ∀ a ∈ U, ∀ x ∈ F, a x ∈ F)
    (a : U) (x : E) :
    quoU U F hU a (Submodule.Quotient.mk x) = Submodule.Quotient.mk ((a : End ℂ E) x) := rfl

/-- `g ↦ (x ↦ g(x̄))`; its range is the space of maps killing `F` with values in `F`. -/
def psi (F : Submodule ℂ E) : (E ⧸ F →ₗ[ℂ] F) →ₗ[ℂ] End ℂ E where
  toFun g := F.subtype ∘ₗ g ∘ₗ F.mkQ
  map_add' g h := by ext; simp
  map_smul' c g := by ext; simp

theorem psi_apply (F : Submodule ℂ E) (g : E ⧸ F →ₗ[ℂ] F) (x : E) :
    psi F g x = (g (Submodule.Quotient.mk x) : E) := rfl

theorem mem_range_psi (F : Submodule ℂ E) (a : End ℂ E) (h1 : ∀ x, a x ∈ F) (h2 : ∀ x ∈ F, a x = 0) :
    a ∈ LinearMap.range (psi F) := by
  refine ⟨F.liftQ (LinearMap.codRestrict F a h1) (fun x hx => ?_), ?_⟩
  · simp [LinearMap.mem_ker, h2 x hx]
  · ext x; simp [psi_apply]

/-- Rank–nullity twice: for `f : P → Q` and `g : P → R`. -/
theorem rank_two {P Q R : Type*} [AddCommGroup P] [Module ℂ P] [FiniteDimensional ℂ P] [AddCommGroup Q]
    [Module ℂ Q] [AddCommGroup R] [Module ℂ R] (f : P →ₗ[ℂ] Q) (g : P →ₗ[ℂ] R) :
    finrank ℂ P = finrank ℂ (LinearMap.range f) + finrank ℂ (LinearMap.range (g ∘ₗ (LinearMap.ker f).subtype))
      + finrank ℂ (LinearMap.ker (g ∘ₗ (LinearMap.ker f).subtype)) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 := LinearMap.finrank_range_add_finrank_ker (g ∘ₗ (LinearMap.ker f).subtype)
  omega

/-- Two applications of rank–nullity: `dim U ≤ dim U″ + r + k`, `r ≤ dim U′`, `k ≤ dim K₀`, with the
information needed for the equality case. -/
theorem count [FiniteDimensional ℂ E] (U : Submodule ℂ (End ℂ E)) (F : Submodule ℂ E)
    (hU : ∀ a ∈ U, ∀ x ∈ F, a x ∈ F) :
    ∃ r k, finrank ℂ U = finrank ℂ (LinearMap.range (quoU U F hU)) + r + k ∧
      r ≤ finrank ℂ (LinearMap.range (resU U F hU)) ∧ k ≤ finrank ℂ (LinearMap.range (psi F)) ∧
      (0 < r → ∃ a ∈ U, (∀ x, a x ∈ F) ∧ ∃ y ∈ F, a y ≠ 0) ∧
      (finrank ℂ (LinearMap.range (psi F)) ≤ k → LinearMap.range (psi F) ≤ U) := by
  have h12 := rank_two (quoU U F hU) (resU U F hU)
  generalize hN : LinearMap.ker (quoU U F hU) = N at h12
  have inF : ∀ q : N, ∀ x, ((q : U) : End ℂ E) x ∈ F := fun q x => by
    have hq : (q : U) ∈ LinearMap.ker (quoU U F hU) := by rw [hN]; exact q.2
    have := LinearMap.congr_fun (LinearMap.mem_ker.1 hq) (Submodule.Quotient.mk x)
    rwa [quoU_apply, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero] at this
  generalize hφ : resU U F hU ∘ₗ N.subtype = φ at h12
  let ι : LinearMap.ker φ →ₗ[ℂ] End ℂ E := U.subtype ∘ₗ N.subtype ∘ₗ (LinearMap.ker φ).subtype
  have hιinj : Function.Injective ι :=
    U.injective_subtype.comp (N.injective_subtype.comp (Submodule.injective_subtype _))
  have hrange : LinearMap.range ι ≤ LinearMap.range (psi F) := by
    rintro _ ⟨p, rfl⟩
    refine mem_range_psi F _ (inF p.1) (fun x hx => ?_)
    have h0 : (resU U F hU ∘ₗ N.subtype) p.1 = 0 := by rw [hφ]; exact LinearMap.mem_ker.1 p.2
    exact congrArg (fun g : End ℂ F => ((g ⟨x, hx⟩ : F) : E)) h0
  have hk := LinearMap.finrank_range_of_inj hιinj
  refine ⟨finrank ℂ (LinearMap.range φ), finrank ℂ (LinearMap.ker φ), by omega,
    hφ ▸ Submodule.finrank_mono (LinearMap.range_comp_le_range _ _), hk ▸ Submodule.finrank_mono hrange,
    fun hr => ?_, fun hle => ?_⟩
  · have hφ0 : φ ≠ 0 := by
      rintro h0; rw [h0, LinearMap.range_zero, finrank_bot] at hr; exact lt_irrefl _ hr
    obtain ⟨q, hq⟩ := DFunLike.ne_iff.1 hφ0
    rw [← hφ] at hq
    obtain ⟨y, hy⟩ := DFunLike.ne_iff.1 hq
    exact ⟨((q : U) : End ℂ E), (q : U).2, inF q, y.1, y.2, fun h0 => hy (Subtype.ext h0)⟩
  · rw [← Submodule.eq_of_le_of_finrank_le hrange (hk ▸ hle)]
    exact (LinearMap.range_comp_le_range _ _).trans (by rw [Submodule.range_subtype])

/-- If `a(E) ⊆ F` and `a` is non-zero on `F ≠ E`, some map killing `F` with values in `F` does not commute
with `a`. -/
theorem not_comm (F : Submodule ℂ E) (hF : F ≠ ⊤) (a : End ℂ E) (ha : ∀ x, a x ∈ F) (y : E) (hy : y ∈ F)
    (hay : a y ≠ 0) : ∃ b ∈ LinearMap.range (psi F), a * b ≠ b * a := by
  have : Nontrivial (E ⧸ F) := Submodule.Quotient.nontrivial_iff.2 hF
  obtain ⟨q, hq⟩ := exists_ne (0 : E ⧸ F)
  obtain ⟨χ, hχ⟩ : ∃ χ : Module.Dual ℂ (E ⧸ F), χ q ≠ 0 := by
    by_contra hc; push Not at hc; exact hq ((Module.forall_dual_apply_eq_zero_iff ℂ q).1 hc)
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective F q
  refine ⟨psi F (χ.smulRight ⟨y, hy⟩), LinearMap.mem_range_self _ _, fun hab => ?_⟩
  have := LinearMap.congr_fun hab x
  rw [Module.End.mul_apply, Module.End.mul_apply, psi_apply, psi_apply,
    (Submodule.Quotient.mk_eq_zero F).2 (ha x)] at this
  simp at this
  exact this.elim (fun h0 => hχ (by simpa using h0)) hay

theorem main : ∀ n : ℕ, ∀ (E : Type u) [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E],
    finrank ℂ E = n → ∀ U V : Submodule ℂ (End ℂ E), (∀ a ∈ U, ∀ b ∈ V, a * b = b * a) →
    finrank ℂ U + finrank ℂ V ≤ n ^ 2 + 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro E _ _ _ hn U V h
  -- reduction to `U ⊆ V`, through `(U ∩ V, U + V)`
  suffices key : ∀ U V : Submodule ℂ (End ℂ E), U ≤ V → (∀ a ∈ U, ∀ b ∈ V, a * b = b * a) →
      finrank ℂ U + finrank ℂ V ≤ n ^ 2 + 1 by
    have := Submodule.finrank_sup_add_finrank_inf_eq U V
    have h' := key (U ⊓ V) (U ⊔ V) (inf_le_left.trans le_sup_left) (by
      intro a ha b hb
      obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hb
      rw [mul_add, add_mul, h a (Submodule.mem_inf.1 ha).1 v hv, h u hu a (Submodule.mem_inf.1 ha).2])
    omega
  clear U V h
  intro U V hUV h
  have hEnd : finrank ℂ (End ℂ E) = n * n := by rw [← hn]; exact Module.finrank_linearMap ℂ ℂ E E
  by_cases hU1 : U ≤ Submodule.span ℂ {1}
  · have h1 : finrank ℂ U ≤ 1 :=
      (Submodule.finrank_mono hU1).trans ((finrank_span_le_card _).trans (by simp))
    have h2 := Submodule.finrank_le V
    rw [hEnd] at h2; nlinarith
  obtain ⟨m, hmU, hm1⟩ := SetLike.not_le_iff_exists.1 hU1
  have : Nontrivial E := by
    by_contra hE
    rw [not_nontrivial_iff_subsingleton] at hE
    exact hm1 (by rw [Subsingleton.elim m 0]; exact zero_mem _)
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue m
  -- `F = ker (m − μ)`, a proper non-zero subspace preserved by `U` and `V`
  set F := m.eigenspace μ with hFdef
  have hFbot : F ≠ ⊥ := hμ
  have hFtop : F ≠ ⊤ := by
    intro htop
    apply hm1
    have : m = μ • (1 : End ℂ E) := by
      ext x
      have hx : x ∈ F := htop ▸ Submodule.mem_top
      simpa using Module.End.mem_eigenspace_iff.1 hx
    rw [this]; exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  have stab : ∀ b : End ℂ E, m * b = b * m → ∀ x ∈ F, b x ∈ F := by
    intro b hb x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    rw [← Module.End.mul_apply, hb, Module.End.mul_apply, hx, map_smul]
  have hV : ∀ b ∈ V, ∀ x ∈ F, b x ∈ F := fun b hb => stab b (h m hmU b hb)
  have hU : ∀ a ∈ U, ∀ x ∈ F, a x ∈ F := fun a ha => hV a (hUV ha)
  have hfg := Submodule.finrank_quotient_add_finrank F
  have hf0 : 0 < finrank ℂ F := by
    rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]; exact hFbot
  have : Nontrivial (E ⧸ F) := Submodule.Quotient.nontrivial_iff.2 hFtop
  have hg0 : 0 < finrank ℂ (E ⧸ F) := Module.finrank_pos
  -- induction on `F` and on `E ⧸ F`
  have ih1 := ih (finrank ℂ F) (by omega) F rfl (LinearMap.range (resU U F hU))
    (LinearMap.range (resU V F hV)) (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      ext x
      simp only [Module.End.mul_apply, resU_apply]
      exact LinearMap.congr_fun (h a a.2 b b.2) x)
  have ih2 := ih (finrank ℂ (E ⧸ F)) (by omega) (E ⧸ F) rfl (LinearMap.range (quoU U F hU))
    (LinearMap.range (quoU V F hV)) (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      ext x
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Module.End.mul_apply,
        quoU_apply]
      rw [← Module.End.mul_apply, h a a.2 b b.2, Module.End.mul_apply])
  have hv1 : finrank ℂ (LinearMap.range (resU V F hV)) ≤ finrank ℂ F * finrank ℂ F :=
    (Submodule.finrank_le _).trans (Module.finrank_linearMap ℂ ℂ F F).le
  have hK : finrank ℂ (LinearMap.range (psi F)) ≤ finrank ℂ (E ⧸ F) * finrank ℂ F :=
    (LinearMap.finrank_range_le _).trans (Module.finrank_linearMap ℂ ℂ _ _).le
  obtain ⟨r, k, hu, hr, hk, hr0, -⟩ := count U F hU
  obtain ⟨r', k', hv, hr', hk', -, hkV⟩ := count V F hV
  -- the equality case cannot occur
  have hexcl : r = 0 ∨ k' < finrank ℂ (LinearMap.range (psi F)) := by
    by_contra hc; push Not at hc
    obtain ⟨a, ha, haF, y, hy, hay⟩ := hr0 (Nat.pos_of_ne_zero hc.1)
    obtain ⟨b, hb, hab⟩ := not_comm F hFtop a haF y hy hay
    exact hab (h a ha b (hkV hc.2 hb))
  have hn2 : n ^ 2 = finrank ℂ F * finrank ℂ F + 2 * (finrank ℂ (E ⧸ F) * finrank ℂ F) +
      finrank ℂ (E ⧸ F) * finrank ℂ (E ⧸ F) := by rw [← hn, ← hfg]; ring
  rcases hexcl with h0 | hlt
  · subst h0; nlinarith
  · nlinarith

end RC3_RCE

open DiazModulus RC3_RCE in
theorem solution {E : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (U V : Submodule ℂ (Module.End ℂ E)) (h : ∀ a ∈ U, ∀ b ∈ V, a * b = b * a) :
    Module.finrank ℂ ↥U + Module.finrank ℂ ↥V ≤ Module.finrank ℂ E ^ 2 + 1 :=
  main _ E rfl U V h
