-- Prove2me | solution 1 for BellmanDP.ExistUnique.type_two_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T11:49:53.683534+00:00
-- url     : https://prove2.me/submissions/f4787fba-5ea7-471a-acb5-b06e10897a69

import Mathlib
import Definitions.Def_BellmanDP_ExistUnique_SupEquation
import Definitions.Def_BellmanDP_ExistUnique_EquationTypes

open Filter Topology


namespace BellmanDP.ExistUnique

theorem lub_le_add_t2e {S : Type*} {A B : S → ℝ} {x y K : ℝ}
    (hx : IsLUB (Set.range A) x) (hy : IsLUB (Set.range B) y) (hK : ∀ q, A q ≤ B q + K) :
    x ≤ y + K := by
  apply hx.2
  rintro _ ⟨q, rfl⟩
  have := hy.1 ⟨q, rfl⟩
  have := hK q
  linarith

theorem abs_lub_sub_t2e {S : Type*} {A B : S → ℝ} {x y K : ℝ}
    (hx : IsLUB (Set.range A) x) (hy : IsLUB (Set.range B) y) (hK : ∀ q, |A q - B q| ≤ K) :
    |x - y| ≤ K := by
  have h1 := lub_le_add_t2e hx hy (fun q => by have := (abs_le.mp (hK q)).2; linarith)
  have h2 := lub_le_add_t2e hy hx (fun q => by have := (abs_le.mp (hK q)).1; linarith)
  rw [abs_le]; constructor <;> linarith

theorem t2e_core {N : ℕ} {S : Type*} [Nonempty S]
    (D : Set (EuclideanSpace ℝ (Fin N))) (g G h : EuclideanSpace ℝ (Fin N) → S → ℝ)
    (T : EuclideanSpace ℝ (Fin N) → S → EuclideanSpace ℝ (Fin N))
    (hg : TypeTwo D g h T) (hG : TypeTwo D G h T)
    (f F : EuclideanSpace ℝ (Fin N) → ℝ)
    (hf_bdd : BoundedOnBoundedParts D f) (hf : ∀ p ∈ D, SolvesAt g h T f p)
    (hF_bdd : BoundedOnBoundedParts D F) (hF : ∀ p ∈ D, SolvesAt G h T F p)
    (c a : ℝ) (ha : a < 1) (hh : ∀ p ∈ D, ‖p‖ ≤ c → ∀ q : S, |h p q| ≤ a)
    (hTc : ∀ p ∈ D, ‖p‖ ≤ c → ∀ q : S, ‖T p q‖ ≤ c) :
    ∀ p ∈ D, ‖p‖ ≤ c →
      |F p - f p| ≤ radialSup D (fun p q => G p q - g p q) c / (1 - a) := by
  intro p0 hp0 hc0
  set u := radialSup D (fun p q => G p q - g p q) c with hu_def
  obtain ⟨Mg, hMg⟩ := hg.g_bdd c
  obtain ⟨MG, hMG⟩ := hG.g_bdd c
  have hu : ∀ p ∈ D, ‖p‖ ≤ c → ∀ q, |G p q - g p q| ≤ u := by
    intro p hp hpc q
    apply le_csSup
    · refine ⟨MG + Mg, ?_⟩
      rintro x ⟨p', hp', hpc', q', rfl⟩
      have := hMg p' hp' hpc' q'
      have := hMG p' hp' hpc' q'
      calc |G p' q' - g p' q'| ≤ |G p' q'| + |g p' q'| := abs_sub _ _
        _ ≤ MG + Mg := by linarith
    · exact ⟨p, hp, hpc, q, rfl⟩
  obtain ⟨Mf, hMf⟩ := hf_bdd c
  obtain ⟨MF, hMF⟩ := hF_bdd c
  set E := sSup {x : ℝ | ∃ p ∈ D, ‖p‖ ≤ c ∧ x = |F p - f p|} with hE_def
  have hbdd : BddAbove {x : ℝ | ∃ p ∈ D, ‖p‖ ≤ c ∧ x = |F p - f p|} := by
    refine ⟨MF + Mf, ?_⟩
    rintro x ⟨p', hp', hpc', rfl⟩
    have := hMf p' hp' hpc'
    have := hMF p' hp' hpc'
    calc |F p' - f p'| ≤ |F p'| + |f p'| := abs_sub _ _
      _ ≤ MF + Mf := by linarith
  have hE : ∀ p ∈ D, ‖p‖ ≤ c → |F p - f p| ≤ E := fun p hp hpc =>
    le_csSup hbdd (show |F p - f p| ∈ {x : ℝ | ∃ p ∈ D, ‖p‖ ≤ c ∧ x = |F p - f p|} from ⟨p, hp, hpc, rfl⟩)
  have hE0 : 0 ≤ E := le_trans (abs_nonneg _) (hE p0 hp0 hc0)
  have ha0 : 0 ≤ a := le_trans (abs_nonneg _) (hh p0 hp0 hc0 (Classical.arbitrary S))
  have hstep : ∀ p ∈ D, ‖p‖ ≤ c → |F p - f p| ≤ u + a * E := by
    intro p hp hpc
    apply abs_lub_sub_t2e (hF p hp) (hf p hp)
    intro q
    simp only [stageReturn]
    have h1 := hu p hp hpc q
    have h2 := hE (T p q) (hg.mapsTo p hp q) (hTc p hp hpc q)
    have h3 := hh p hp hpc q
    have h4 : |h p q * (F (T p q) - f (T p q))| ≤ a * E := by
      rw [abs_mul]; exact mul_le_mul h3 h2 (abs_nonneg _) ha0
    calc |G p q + h p q * F (T p q) - (g p q + h p q * f (T p q))|
        = |(G p q - g p q) + h p q * (F (T p q) - f (T p q))| := by ring_nf
      _ ≤ |G p q - g p q| + |h p q * (F (T p q) - f (T p q))| := abs_add_le _ _
      _ ≤ u + a * E := by linarith
  have hEle : E ≤ u + a * E := by
    apply csSup_le (⟨_, p0, hp0, hc0, rfl⟩ : Set.Nonempty {x : ℝ | ∃ p ∈ D, ‖p‖ ≤ c ∧ x = |F p - f p|})
    intro x hx
    obtain ⟨p', hp', hpc', rfl⟩ := hx
    exact hstep p' hp' hpc'
  rw [le_div_iff₀ (by linarith)]
  have := hE p0 hp0 hc0
  nlinarith


theorem abs_iSup_le_t2e {S : Type*} [Nonempty S] {A : S → ℝ} {B : ℝ} (hA : ∀ q, |A q| ≤ B) :
    |⨆ q, A q| ≤ B := by
  have hb : BddAbove (Set.range A) := ⟨B, by rintro _ ⟨q, rfl⟩; exact (abs_le.mp (hA q)).2⟩
  rw [abs_le]; constructor
  · have q := Classical.arbitrary S
    exact le_trans (abs_le.mp (hA q)).1 (le_ciSup hb q)
  · exact ciSup_le (fun q => (abs_le.mp (hA q)).2)

theorem abs_iSup_sub_t2e {S : Type*} [Nonempty S] {A A' : S → ℝ} {K : ℝ}
    (hA : BddAbove (Set.range A)) (hA' : BddAbove (Set.range A'))
    (hK : ∀ q, |A q - A' q| ≤ K) : |(⨆ q, A q) - ⨆ q, A' q| ≤ K :=
  abs_lub_sub_t2e (isLUB_ciSup hA) (isLUB_ciSup hA') hK

theorem bdd_of_abs_t2e {S : Type*} {A : S → ℝ} {B : ℝ} (hA : ∀ q, |A q| ≤ B) :
    BddAbove (Set.range A) := ⟨B, by rintro _ ⟨q, rfl⟩; exact (abs_le.mp (hA q)).2⟩

section Frame

variable {N : ℕ} {S : Type*} [Nonempty S]
    (D : Set (EuclideanSpace ℝ (Fin N))) (g h : EuclideanSpace ℝ (Fin N) → S → ℝ)
    (T : EuclideanSpace ℝ (Fin N) → S → EuclideanSpace ℝ (Fin N)) (c a Mg : ℝ)

/-- standing hypotheses on the invariant region `K = D ∩ {‖p‖ ≤ c}` -/
structure FrameT2e : Prop where
  inv : ∀ p ∈ D, ‖p‖ ≤ c → ∀ q, T p q ∈ D ∧ ‖T p q‖ ≤ c
  a0 : 0 ≤ a
  a1 : a < 1
  hh : ∀ p ∈ D, ‖p‖ ≤ c → ∀ q, |h p q| ≤ a
  M0 : 0 ≤ Mg
  hg : ∀ p ∈ D, ‖p‖ ≤ c → ∀ q, |g p q| ≤ Mg

variable {D g h T c a Mg}

theorem fr_bound (H : FrameT2e D g h T c a Mg) :
    ∀ n, ∀ p ∈ D, ‖p‖ ≤ c → |succApprox g h T (supG g) n p| ≤ Mg / (1 - a) := by
  have h1a : 0 < 1 - a := by linarith [H.a1]
  have hB : Mg ≤ Mg / (1 - a) := by
    rw [le_div_iff₀ h1a]; nlinarith [H.M0, H.a0]
  have hB0 : 0 ≤ Mg / (1 - a) := div_nonneg H.M0 h1a.le
  have hfix : Mg + a * (Mg / (1 - a)) = Mg / (1 - a) := by field_simp; ring
  intro n
  induction n with
  | zero =>
    intro p hp hpc
    exact (abs_iSup_le_t2e (fun q => H.hg p hp hpc q)).trans hB
  | succ n ih =>
    intro p hp hpc
    show |⨆ q, stageReturn g h T (succApprox g h T (supG g) n) p q| ≤ _
    apply abs_iSup_le_t2e
    intro q
    obtain ⟨hTD, hTc⟩ := H.inv p hp hpc q
    have e1 := H.hg p hp hpc q
    have e2 := ih _ hTD hTc
    have e3 := H.hh p hp hpc q
    simp only [stageReturn]
    calc |g p q + h p q * succApprox g h T (supG g) n (T p q)|
        ≤ |g p q| + |h p q| * |succApprox g h T (supG g) n (T p q)| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ Mg + a * (Mg / (1 - a)) := by
          have := H.a0
          gcongr
      _ = _ := hfix

theorem fr_stage_bdd (H : FrameT2e D g h T c a Mg) (n : ℕ) (p) (hp : p ∈ D) (hpc : ‖p‖ ≤ c) :
    ∀ q, |stageReturn g h T (succApprox g h T (supG g) n) p q| ≤ Mg + a * (Mg / (1 - a)) := by
  intro q
  obtain ⟨hTD, hTc⟩ := H.inv p hp hpc q
  have e1 := H.hg p hp hpc q
  have e2 := fr_bound H n _ hTD hTc
  have e3 := H.hh p hp hpc q
  simp only [stageReturn]
  calc |g p q + h p q * succApprox g h T (supG g) n (T p q)|
      ≤ |g p q| + |h p q| * |succApprox g h T (supG g) n (T p q)| := by
        rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ Mg + a * (Mg / (1 - a)) := by have := H.a0; gcongr

theorem fr_diff (H : FrameT2e D g h T c a Mg) :
    ∀ n, ∀ p ∈ D, ‖p‖ ≤ c →
      |succApprox g h T (supG g) (n + 1) p - succApprox g h T (supG g) n p| ≤ 2 * (Mg / (1 - a)) * a ^ n := by
  intro n
  induction n with
  | zero =>
    intro p hp hpc
    have e1 := fr_bound H 1 p hp hpc
    have e2 := fr_bound H 0 p hp hpc
    simp only [pow_zero, mul_one]
    calc _ ≤ |succApprox g h T (supG g) (0 + 1) p| + |succApprox g h T (supG g) 0 p| := abs_sub _ _
      _ ≤ _ := by linarith
  | succ n ih =>
    intro p hp hpc
    show |(⨆ q, stageReturn g h T (succApprox g h T (supG g) (n + 1)) p q)
      - ⨆ q, stageReturn g h T (succApprox g h T (supG g) n) p q| ≤ _
    apply abs_iSup_sub_t2e (bdd_of_abs_t2e (fr_stage_bdd H (n + 1) p hp hpc))
      (bdd_of_abs_t2e (fr_stage_bdd H n p hp hpc))
    intro q
    obtain ⟨hTD, hTc⟩ := H.inv p hp hpc q
    have e2 := ih _ hTD hTc
    have e3 := H.hh p hp hpc q
    simp only [stageReturn]
    have : g p q + h p q * succApprox g h T (supG g) (n + 1) (T p q) -
        (g p q + h p q * succApprox g h T (supG g) n (T p q)) =
        h p q * (succApprox g h T (supG g) (n + 1) (T p q) - succApprox g h T (supG g) n (T p q)) := by ring
    rw [this, abs_mul]
    calc _ ≤ a * (2 * (Mg / (1 - a)) * a ^ n) := mul_le_mul e3 e2 (abs_nonneg _) H.a0
      _ = _ := by ring

theorem fr_cauchy (H : FrameT2e D g h T c a Mg) (p) (hp : p ∈ D) (hpc : ‖p‖ ≤ c) :
    CauchySeq (fun n => succApprox g h T (supG g) n p) := by
  apply cauchySeq_of_le_geometric a (2 * (Mg / (1 - a))) H.a1
  intro n
  rw [Real.dist_eq, abs_sub_comm]
  exact fr_diff H n p hp hpc

theorem fr_est (H : FrameT2e D g h T c a Mg) (p) (hp : p ∈ D) (hpc : ‖p‖ ≤ c) (n : ℕ) :
    |succApprox g h T (supG g) n p - limUnder atTop (fun n => succApprox g h T (supG g) n p)|
      ≤ 2 * (Mg / (1 - a)) * a ^ n / (1 - a) := by
  have := dist_le_of_le_geometric_of_tendsto a (2 * (Mg / (1 - a))) H.a1
    (fun n => by rw [Real.dist_eq, abs_sub_comm]; exact fr_diff H n p hp hpc)
    (fr_cauchy H p hp hpc).tendsto_limUnder n
  rwa [Real.dist_eq] at this

theorem fr_err_tendsto (H : FrameT2e D g h T c a Mg) :
    Tendsto (fun n : ℕ => 2 * (Mg / (1 - a)) * a ^ n / (1 - a)) atTop (𝓝 0) := by
  have := ((tendsto_pow_atTop_nhds_zero_of_lt_one H.a0 H.a1).const_mul (2 * (Mg / (1 - a)))).div_const (1 - a)
  simpa using this

theorem fr_err_nonneg (H : FrameT2e D g h T c a Mg) (n : ℕ) :
    0 ≤ 2 * (Mg / (1 - a)) * a ^ n / (1 - a) := by
  have h1a : 0 < 1 - a := by linarith [H.a1]
  have := H.M0; have := H.a0
  positivity

theorem fr_solves (H : FrameT2e D g h T c a Mg) (f : EuclideanSpace ℝ (Fin N) → ℝ)
    (hf : ∀ p, f p = limUnder atTop (fun n => succApprox g h T (supG g) n p))
    (p) (hp : p ∈ D) (hpc : ‖p‖ ≤ c) : SolvesAt g h T f p := by
  set e : ℕ → ℝ := fun n => 2 * (Mg / (1 - a)) * a ^ n / (1 - a) with he
  have hest : ∀ n, ∀ x ∈ D, ‖x‖ ≤ c → |succApprox g h T (supG g) n x - f x| ≤ e n := by
    intro n x hx hxc; rw [hf]; exact fr_est H x hx hxc n
  have he0 : ∀ n, 0 ≤ e n := fr_err_nonneg H
  have hlim : Tendsto (fun n => succApprox g h T (supG g) (n + 1) p) atTop (𝓝 (f p)) := by
    rw [hf]; exact ((fr_cauchy H p hp hpc).tendsto_limUnder).comp (tendsto_add_atTop_nat 1)
  have hcmp : ∀ n q, |stageReturn g h T f p q - stageReturn g h T (succApprox g h T (supG g) n) p q| ≤ e n := by
    intro n q
    obtain ⟨hTD, hTc⟩ := H.inv p hp hpc q
    have e2 := hest n _ hTD hTc
    have e3 := H.hh p hp hpc q
    have ha1 : a ≤ 1 := H.a1.le
    simp only [stageReturn]
    have : g p q + h p q * f (T p q) - (g p q + h p q * succApprox g h T (supG g) n (T p q)) =
        - (h p q * (succApprox g h T (supG g) n (T p q) - f (T p q))) := by ring
    rw [this, abs_neg, abs_mul]
    calc _ ≤ 1 * e n := mul_le_mul (e3.trans ha1) e2 (abs_nonneg _) zero_le_one
      _ = e n := one_mul _
  have hsup : ∀ n, succApprox g h T (supG g) (n + 1) p = ⨆ q, stageReturn g h T (succApprox g h T (supG g) n) p q :=
    fun n => rfl
  constructor
  · rintro _ ⟨q, rfl⟩
    have h1 : Tendsto (fun n => succApprox g h T (supG g) (n + 1) p + e n) atTop (𝓝 (f p)) := by
      simpa using hlim.add (fr_err_tendsto H)
    apply ge_of_tendsto' h1
    intro n
    have := (abs_le.mp (hcmp n q)).2
    have h2 : stageReturn g h T (succApprox g h T (supG g) n) p q ≤ succApprox g h T (supG g) (n + 1) p := by
      rw [hsup]; exact le_ciSup (bdd_of_abs_t2e (fr_stage_bdd H n p hp hpc)) q
    linarith
  · intro b hb
    have h1 : Tendsto (fun n => succApprox g h T (supG g) (n + 1) p - e n) atTop (𝓝 (f p)) := by
      simpa using hlim.sub (fr_err_tendsto H)
    apply le_of_tendsto' h1
    intro n
    have : succApprox g h T (supG g) (n + 1) p ≤ b + e n := by
      rw [hsup]
      apply ciSup_le
      intro q
      have := (abs_le.mp (hcmp n q)).1
      have := hb ⟨q, rfl⟩
      linarith
    linarith

theorem fr_fbound (H : FrameT2e D g h T c a Mg) (f : EuclideanSpace ℝ (Fin N) → ℝ)
    (hf : ∀ p, f p = limUnder atTop (fun n => succApprox g h T (supG g) n p))
    (p) (hp : p ∈ D) (hpc : ‖p‖ ≤ c) : |f p| ≤ Mg / (1 - a) := by
  have hlim : Tendsto (fun n => succApprox g h T (supG g) n p) atTop (𝓝 (f p)) := by
    rw [hf]; exact (fr_cauchy H p hp hpc).tendsto_limUnder
  exact le_of_tendsto' hlim.abs (fun n => fr_bound H n p hp hpc)

/-- uniform continuity on the region -/
def UCK_t2e (D : Set (EuclideanSpace ℝ (Fin N))) (c : ℝ) (φ : EuclideanSpace ℝ (Fin N) → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ p ∈ D, ‖p‖ ≤ c → ∀ p' ∈ D, ‖p'‖ ≤ c → dist p p' < δ → |φ p - φ p'| ≤ ε

theorem fr_uc (H : FrameT2e D g h T c a Mg) (hgU : UnifContInP D g) (hhU : UnifContInP D h)
    (hTU : UnifContInP D T) : ∀ n, UCK_t2e D c (succApprox g h T (supG g) n) := by
  intro n
  induction n with
  | zero =>
    intro ε hε
    obtain ⟨δ, hδ, hδg⟩ := hgU c ε hε
    refine ⟨δ, hδ, fun p hp hpc p' hp' hpc' hd => ?_⟩
    show |(⨆ q, g p q) - ⨆ q, g p' q| ≤ ε
    apply abs_iSup_sub_t2e (bdd_of_abs_t2e (H.hg p hp hpc)) (bdd_of_abs_t2e (H.hg p' hp' hpc'))
    intro q
    have := hδg p hp p' hp' hpc hpc' hd q
    rw [Real.dist_eq] at this; exact this.le
  | succ n ih =>
    intro ε hε
    set B := Mg / (1 - a) with hBdef
    have hB0 : 0 ≤ B := div_nonneg H.M0 (by linarith [H.a1])
    obtain ⟨δg, hδg, hg'⟩ := hgU c (ε / 3) (by linarith)
    obtain ⟨δh, hδh, hh'⟩ := hhU c (ε / (3 * (B + 1))) (by positivity)
    obtain ⟨δ3, hδ3, h3⟩ := ih (ε / 3) (by linarith)
    obtain ⟨δT, hδT, hT'⟩ := hTU c δ3 hδ3
    refine ⟨min δg (min δh δT), by positivity, fun p hp hpc p' hp' hpc' hd => ?_⟩
    have hdg : dist p p' < δg := lt_of_lt_of_le hd (min_le_left _ _)
    have hdh : dist p p' < δh := lt_of_lt_of_le hd ((min_le_right _ _).trans (min_le_left _ _))
    have hdT : dist p p' < δT := lt_of_lt_of_le hd ((min_le_right _ _).trans (min_le_right _ _))
    show |(⨆ q, stageReturn g h T (succApprox g h T (supG g) n) p q)
      - ⨆ q, stageReturn g h T (succApprox g h T (supG g) n) p' q| ≤ ε
    apply abs_iSup_sub_t2e (bdd_of_abs_t2e (fr_stage_bdd H n p hp hpc))
      (bdd_of_abs_t2e (fr_stage_bdd H n p' hp' hpc'))
    intro q
    obtain ⟨hTD, hTc⟩ := H.inv p hp hpc q
    obtain ⟨hTD', hTc'⟩ := H.inv p' hp' hpc' q
    have e1 := hg' p hp p' hp' hpc hpc' hdg q
    have e2 := hh' p hp p' hp' hpc hpc' hdh q
    have e3 := h3 _ hTD hTc _ hTD' hTc' (hT' p hp p' hp' hpc hpc' hdT q)
    have e4 := fr_bound H n _ hTD hTc
    have e5 := H.hh p' hp' hpc' q
    rw [Real.dist_eq] at e1 e2
    simp only [stageReturn]
    set X := succApprox g h T (supG g) n (T p q)
    set Y := succApprox g h T (supG g) n (T p' q)
    have : g p q + h p q * X - (g p' q + h p' q * Y) =
        (g p q - g p' q) + (h p q - h p' q) * X + h p' q * (X - Y) := by ring
    rw [this]
    have k1 : |(h p q - h p' q) * X| ≤ ε / (3 * (B + 1)) * B := by
      rw [abs_mul]; exact mul_le_mul e2.le e4 (abs_nonneg _) (by positivity)
    have k2 : ε / (3 * (B + 1)) * B ≤ ε / 3 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have k3 : |h p' q * (X - Y)| ≤ 1 * (ε / 3) := by
      rw [abs_mul]; exact mul_le_mul (e5.trans H.a1.le) e3 (abs_nonneg _) zero_le_one
    calc _ ≤ |(g p q - g p' q) + (h p q - h p' q) * X| + |h p' q * (X - Y)| := abs_add_le _ _
      _ ≤ |g p q - g p' q| + |(h p q - h p' q) * X| + |h p' q * (X - Y)| := by
          gcongr; exact abs_add_le _ _
      _ ≤ ε := by linarith

theorem fr_cont (H : FrameT2e D g h T c a Mg) (hgU : UnifContInP D g) (hhU : UnifContInP D h)
    (hTU : UnifContInP D T) (f : EuclideanSpace ℝ (Fin N) → ℝ)
    (hf : ∀ p, f p = limUnder atTop (fun n => succApprox g h T (supG g) n p)) :
    ContinuousOn f (D ∩ Metric.closedBall 0 c) := by
  rw [Metric.continuousOn_iff]
  intro b hb ε hε
  have hb' : b ∈ D ∧ ‖b‖ ≤ c := ⟨hb.1, by simpa using hb.2⟩
  obtain ⟨n, hn⟩ := ((fr_err_tendsto H).eventually (gt_mem_nhds (show (0:ℝ) < ε / 4 by linarith))).exists
  obtain ⟨δ, hδ, hδu⟩ := fr_uc H hgU hhU hTU n (ε / 4) (by linarith)
  refine ⟨δ, hδ, fun x hx hd => ?_⟩
  have hx' : x ∈ D ∧ ‖x‖ ≤ c := ⟨hx.1, by simpa using hx.2⟩
  have e1 := fr_est H x hx'.1 hx'.2 n
  have e2 := fr_est H b hb'.1 hb'.2 n
  rw [← hf] at e1 e2
  have e3 := hδu x hx'.1 hx'.2 b hb'.1 hb'.2 hd
  rw [Real.dist_eq]
  calc |f x - f b| = |(succApprox g h T (supG g) n x - f b) - (succApprox g h T (supG g) n x - f x)| := by ring_nf
    _ ≤ |succApprox g h T (supG g) n x - f b| + |succApprox g h T (supG g) n x - f x| := abs_sub _ _
    _ = |(succApprox g h T (supG g) n x - succApprox g h T (supG g) n b) + (succApprox g h T (supG g) n b - f b)|
          + |succApprox g h T (supG g) n x - f x| := by ring_nf
    _ ≤ |succApprox g h T (supG g) n x - succApprox g h T (supG g) n b| + |succApprox g h T (supG g) n b - f b|
          + |succApprox g h T (supG g) n x - f x| := by gcongr; exact abs_add_le _ _
    _ < ε := by linarith

end Frame

theorem frame_exists_t2e {N : ℕ} {S : Type*} {D : Set (EuclideanSpace ℝ (Fin N))}
    {g h : EuclideanSpace ℝ (Fin N) → S → ℝ}
    {T : EuclideanSpace ℝ (Fin N) → S → EuclideanSpace ℝ (Fin N)}
    (hType : TypeTwo D g h T) (c : ℝ) : ∃ c' ≥ c, ∃ a Mg, FrameT2e D g h T c' a Mg := by
  have hinv : ∃ c' ≥ c, ∀ p ∈ D, ‖p‖ ≤ c' → ∀ q, T p q ∈ D ∧ ‖T p q‖ ≤ c' := by
    rcases hType.T_cond with h1 | hb
    · exact ⟨c, le_rfl, fun p hp hpc q => ⟨hType.mapsTo p hp q, (h1 p hp q).trans hpc⟩⟩
    · obtain ⟨R, hR⟩ := hb.subset_closedBall 0
      refine ⟨max c R, le_max_left _ _, fun p hp hpc q => ⟨hType.mapsTo p hp q, ?_⟩⟩
      have := hR (hType.mapsTo p hp q)
      rw [mem_closedBall_zero_iff] at this
      exact this.trans (le_max_right _ _)
  obtain ⟨c', hc', hinv⟩ := hinv
  obtain ⟨a, ha1, hha⟩ := hType.h_contract c'
  obtain ⟨Mg, hMg⟩ := hType.g_bdd c'
  refine ⟨c', hc', max a 0, max Mg 0, ⟨hinv, le_max_right _ _, max_lt ha1 one_pos,
    fun p hp hpc q => (hha p hp hpc q).trans (le_max_left _ _), le_max_right _ _,
    fun p hp hpc q => (hMg p hp hpc q).trans (le_max_left _ _)⟩⟩

theorem t2e_main {N : ℕ} {S : Type*} [Nonempty S]
    (D : Set (EuclideanSpace ℝ (Fin N))) (g h : EuclideanSpace ℝ (Fin N) → S → ℝ)
    (T : EuclideanSpace ℝ (Fin N) → S → EuclideanSpace ℝ (Fin N))
    (hType : TypeTwo D g h T) :
    ∃ f : EuclideanSpace ℝ (Fin N) → ℝ,
      (BoundedOnBoundedParts D f ∧ ∀ p ∈ D, SolvesAt g h T f p) ∧
      (∀ F : EuclideanSpace ℝ (Fin N) → ℝ, BoundedOnBoundedParts D F →
        (∀ p ∈ D, SolvesAt g h T F p) → ∀ p ∈ D, F p = f p) ∧
      (∀ p ∈ D, Tendsto (fun n => succApprox g h T (supG g) n p) atTop (𝓝 (f p))) ∧
      (UnifContInP D g → UnifContInP D h → UnifContInP D T →
        ∀ c : ℝ, ContinuousOn f (D ∩ Metric.closedBall 0 c)) := by
  set f : EuclideanSpace ℝ (Fin N) → ℝ := fun p => limUnder atTop (fun n => succApprox g h T (supG g) n p) with hfdef
  have hf : ∀ p, f p = limUnder atTop (fun n => succApprox g h T (supG g) n p) := fun p => rfl
  have hbdd : BoundedOnBoundedParts D f := by
    intro c
    obtain ⟨c', hc', a, Mg, H⟩ := frame_exists_t2e hType c
    exact ⟨Mg / (1 - a), fun p hp hpc => fr_fbound H f hf p hp (hpc.trans hc')⟩
  have hsol : ∀ p ∈ D, SolvesAt g h T f p := by
    intro p hp
    obtain ⟨c', hc', a, Mg, H⟩ := frame_exists_t2e hType ‖p‖
    exact fr_solves H f hf p hp hc'
  refine ⟨f, ⟨hbdd, hsol⟩, ?_, ?_, ?_⟩
  · intro F hF_bdd hF p hp
    obtain ⟨c', hc', a, Mg, H⟩ := frame_exists_t2e hType ‖p‖
    have := t2e_core D g g h T hType hType f F hbdd hsol hF_bdd hF c' a H.a1 H.hh
      (fun p hp hpc q => (H.inv p hp hpc q).2) p hp hc'
    have h0 : radialSup D (fun p q => g p q - g p q) c' ≤ 0 := by
      apply Real.sSup_nonpos
      rintro x ⟨p', -, -, q, rfl⟩
      simp
    have h1 : radialSup D (fun p q => g p q - g p q) c' / (1 - a) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg h0 (by linarith [H.a1])
    have := abs_nonpos_iff.mp (this.trans h1)
    linarith
  · intro p hp
    obtain ⟨c', hc', a, Mg, H⟩ := frame_exists_t2e hType ‖p‖
    exact (fr_cauchy H p hp hc').tendsto_limUnder
  · intro hgU hhU hTU c
    obtain ⟨c', hc', a, Mg, H⟩ := frame_exists_t2e hType c
    exact (fr_cont H hgU hhU hTU f hf).mono
      (Set.inter_subset_inter_right D (Metric.closedBall_subset_closedBall hc'))

end BellmanDP.ExistUnique

open BellmanDP.ExistUnique


theorem solution {N : ℕ} {S : Type*} [Nonempty S]
    (D : Set (EuclideanSpace ℝ (Fin N))) (g h : EuclideanSpace ℝ (Fin N) → S → ℝ)
    (T : EuclideanSpace ℝ (Fin N) → S → EuclideanSpace ℝ (Fin N))
    (hType : TypeTwo D g h T) :
    ∃ f : EuclideanSpace ℝ (Fin N) → ℝ,
      (BoundedOnBoundedParts D f ∧ ∀ p ∈ D, SolvesAt g h T f p) ∧
      (∀ F : EuclideanSpace ℝ (Fin N) → ℝ, BoundedOnBoundedParts D F →
        (∀ p ∈ D, SolvesAt g h T F p) → ∀ p ∈ D, F p = f p) ∧
      (∀ p ∈ D, Tendsto (fun n => succApprox g h T (supG g) n p) atTop (𝓝 (f p))) ∧
      (UnifContInP D g → UnifContInP D h → UnifContInP D T →
        ∀ c : ℝ, ContinuousOn f (D ∩ Metric.closedBall 0 c)) := by
  exact t2e_main D g h T hType
